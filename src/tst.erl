%% -*- mode: erlang; erlang-indent-level: 2 -*-
%%% Created : 25 Feb 2011 by mats cronqvist <masse@klarna.com>

%% @doc
%% @end

-module('tst').
-author('mats cronqvist').
-export([go/1]).



-define(SIZE,4).

-record(blob,
        {key,
         data,
         type=term,
         size,
         bin}).

-record(node,
        {pos,
         size=0,
         length=0,
         min_key,
         max_key,
         zero_pos=0,
         bin}).

-record(state,
        {size=?SIZE,
         size2=?SIZE*2,
         eof=0,
         cache=[],
         blobs=[],
         nodes=[[]]}).

go(L) ->
  finalize(lists:foldl(fun add_blob_f/2,#state{},lists:seq(1,L))).

add_blob_f(N,S)->
  add_blob({k,N},{v,N},S).

finalize(S0 = #state{cache=[],blobs=Blobs}) ->
  case length(Blobs) =< S0#state.size of
    true ->
      Leaf = mk_leaf(Blobs,S0#state.eof),
      S2 =
        check_nodes(S0#state{nodes=add_leaf(Leaf,S0),
                             cache=Blobs++[Leaf],
                             eof=Leaf#node.pos+Leaf#node.size,
                             blobs=[]});
    false->
      {Blobs1,Blobs2} = lists:split(length(Blobs) div 2,Blobs),
      Leaf1 = mk_leaf(Blobs1,S0#state.eof),
      S1 =
        check_nodes(S0#state{nodes=add_leaf(Leaf1,S0),
                             cache=Blobs1++[Leaf1],
                             eof=Leaf1#node.pos+Leaf1#node.size,
                             blobs=Blobs2}),
      Leaf2 = mk_leaf(Blobs2,S1#state.eof),
      S2 =
        check_nodes(S1#state{nodes=add_leaf(Leaf2,S1),
                             cache=S1#state.cache++Blobs2++[Leaf2],
                             eof=Leaf2#node.pos+Leaf2#node.size,
                             blobs=[]})
  end,
  flush_cache(finalize_nodes(S2)).

finalize_nodes(S = #state{eof=Eof,cache=Cache,nodes=[Ns]}) ->
  case length(Ns) =< S#state.size of
    true ->
      Root = mk_node(Ns,Eof),
      NewEof = Root#node.pos+Root#node.size,
      S#state{eof=NewEof,cache=Cache++[Root],nodes=[]};
    false->
      {N1s,N2s} = lists:split(length(Ns) div 2,Ns),
      Node1 = mk_node(N1s,Eof),
      NewEof1 = Node1#node.pos+Node1#node.size,
      Node2 = mk_node(N2s,NewEof1),
      NewEof2 = Node2#node.pos+Node2#node.size,
      finalize_nodes(S#state{cache=Cache++[Node1,Node2],
                             nodes=[[Node1,Node2]],
                             eof=NewEof2})
  end;
finalize_nodes(S = #state{eof=Eof,cache=Cache,nodes=[NHs|NTs]}) ->
  case length(NHs) =< S#state.size of
    true ->
      Node = mk_node(NHs,Eof),
      NewEof = Node#node.pos+Node#node.size,
      finalize_nodes(S#state{cache=Cache++[Node],
                             nodes=add_node(Node,NTs),
                             eof=NewEof});
    false->
      {NH1s,NH2s} = lists:split(length(NHs) div 2,NHs),
      Node1 = mk_node(NH1s,Eof),
      NewEof1 = Node1#node.pos+Node1#node.size,
      Node2 = mk_node(NH2s,NewEof1),
      NewEof2 = Node2#node.pos+Node2#node.size,
      finalize_nodes(S#state{cache=Cache++[Node1,Node2],
                             nodes=add_node(Node1,add_node(Node1,NTs)),
                             eof=NewEof2})
  end.

add_blob(Key,Val,S = #state{blobs=Blobs}) ->
  case S#state.size2 < length(Blobs) of
    true ->
      {BlobsH,BlobsT} = lists:split(S#state.size,Blobs),
      NewLeaf = mk_leaf(BlobsH,S#state.eof),
      flush_cache(
        check_nodes(
          S#state{nodes=add_leaf(NewLeaf,S),
                  cache=BlobsH++[NewLeaf],
                  eof=NewLeaf#node.pos+NewLeaf#node.size,
                  blobs=BlobsT++[mk_blob(Key,Val)]}));
    false->
      S#state{blobs=Blobs++[mk_blob(Key,Val)]}
  end.

add_leaf(Leaf,#state{nodes=[Leaves|Ints]}) ->
  [Leaves++[Leaf]|Ints].

check_nodes(S = #state{nodes=Nodes}) ->
  {NewNodes,NewCache,NewEof} = chk_nodes(Nodes,S),
  S#state{nodes=NewNodes,
          cache=S#state.cache++NewCache,
          eof=NewEof}.

chk_nodes(Nodes,#state{size=S,size2=S2,eof=Eof}) ->
  chk_nodes(Nodes,{[],[],Eof},{S,S2}).

chk_nodes([],O,_)         -> O;
chk_nodes([N0s|Nss],{Ns,Cache,Eof},C={S,S2}) ->
  case S2 < length(N0s) of
    true ->
      {NodesH,NodesT} = lists:split(S,N0s),
      Node = mk_node(NodesH,Eof),
      NewEof = Node#node.pos+Node#node.size,
      chk_nodes(add_node(Node,Nss),{Ns++[NodesT],Cache++[Node],NewEof},C);
    false->
      {Ns++[N0s|Nss],Cache,Eof}
  end.

add_node(N,[]) -> [[N]];
add_node(N,[Ns|NT]) -> [Ns++[N]|NT].

mk_blob(Key,Val) ->
  case is_binary(Val) of
    true -> Bin = Val,
            Type = binary;
    false-> Bin = term_to_binary(Val),
            Type = term
  end,
  #blob{key=Key,
        data=Val,
        bin=Bin,
        size=byte_size(Bin),
        type=Type}.

-record(tmp,{eof,recs,len=0,min,max,zp}).

mk_leaf(Blobs,Eof) ->
  T = lists:foldl(fun boff_f/2,#tmp{eof=Eof},Blobs),
  Bin = leaf_disk_format(T),
  #node{length=T#tmp.len,
        size=byte_size(Bin),
        min_key=T#tmp.min,
        max_key=T#tmp.max,
        pos=T#tmp.eof,
        zero_pos=leaf,
        bin=Bin}.

boff_f(#blob{key=Key,size=Size},T = #tmp{len=0,eof=Eof}) ->
  T#tmp{eof=Eof+Size,recs=[{Key,Eof}],len=1,min=Key,max=Key};
boff_f(#blob{key=Key,size=Size},T = #tmp{eof=Eof,len=Len,recs=Recs})->
  T#tmp{eof=Eof+Size,recs=Recs++[{Key,Eof}],len=Len+1,max=Key}.

leaf_disk_format(T) ->
  term_to_binary({T#tmp.len,T#tmp.recs}).

mk_node(Nodes,Eof) ->
  T = lists:foldl(fun noff_f/2,#tmp{},Nodes),
  Bin = int_disk_format(T),
  #node{length=T#tmp.len,
        size=byte_size(Bin),
        min_key=T#tmp.min,
        max_key=T#tmp.max,
        pos=Eof,
        zero_pos=T#tmp.zp,
        bin=Bin}.

noff_f(#node{pos=Pos,min_key=Min,max_key=Max},T = #tmp{len=0})->
  T#tmp{zp=Pos,len=1,min=Min,max=Max,recs=[]};
noff_f(#node{pos=Pos,max_key=Max,min_key=Min},T = #tmp{len=Len,recs=Recs})->
  T#tmp{len=Len+1,max=Max,recs=Recs++[{Pos,Min}]}.

int_disk_format(T) ->
  term_to_binary({T#tmp.len,T#tmp.zp,T#tmp.min,T#tmp.max,T#tmp.recs}).

flush_cache(S) ->
  io:fwrite("FLUSHING:~n~p~n",[[form(I)||I<-S#state.cache]]),
  S#state{cache=[]}.

form(N = #blob{}) -> wrap(blob,N);
form(N = #node{}) -> [{T,unroll_bin(V)}||{T,V}<-wrap(node,N)].

wrap(RecName,Rec) -> 
  lists:zip(rec_info(RecName),tl(tuple_to_list(Rec))).

unroll_bin(B) when is_binary(B) -> binary_to_term(B);
unroll_bin(X) -> X.

rec_info(node) -> record_info(fields,node);
rec_info(blob) -> record_info(fields,blob).
