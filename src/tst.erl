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
         bin,
         size}).

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
         nodes=[[],[]]}).

go(L) ->
  lists:foldl(fun(N,S)->add_blob({k,N},{v,N},S)end,#state{},lists:seq(1,L)).

add_blob(Key,Val,S = #state{blobs=Blobs}) ->
  case S#state.size2 < length(Blobs) of
    true ->
      [Leaves|Ints] = S#state.nodes,
      {BlobsH,BlobsT} = lists:split(S#state.size,Blobs),
      NewLeaf = mk_leaf(BlobsH,S#state.eof),
      flush_cache(
        check_nodes(
          S#state{nodes=[Leaves++[NewLeaf]|Ints],
                  cache=BlobsH++[NewLeaf],
                  eof=NewLeaf#node.pos+NewLeaf#node.size,
                  blobs=BlobsT++[mk_blob(Key,Val)]}));
    false->
      S#state{blobs=Blobs++[mk_blob(Key,Val)]}
  end.

flush_cache(S) ->
  io:fwrite("FLUSHING:~n~p~n",[S#state.cache]),
  S#state{cache=[]}.

check_nodes(S = #state{nodes=Nodes}) ->
  {NewNodes,NewCache,NewEof} = chk_nodes(Nodes,S),
  S#state{nodes=NewNodes,
          cache=S#state.cache++NewCache,
          eof=NewEof}.

chk_nodes(Nodes,#state{size=S,size2=S2,eof=Eof}) ->
  chk_nodes(Nodes,{[],[],Eof},{S,S2}).

chk_nodes([],O,_)         -> O;
chk_nodes([[]|_],O,_)     -> O;
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

-record(tmp,{eof,bbs,len=0,min,max,zp=0}).

mk_leaf(Blobs,Eof) ->
  T = lists:foldl(fun boff_f/2,#tmp{eof=Eof},Blobs),
  Bin = leaf_disk_format(T),
  #node{length=T#tmp.len,
        size=byte_size(Bin),
        min_key=T#tmp.min,
        max_key=T#tmp.max,
        pos=T#tmp.eof,
        bin=Bin}.

boff_f(#blob{key=Key,size=Size},T = #tmp{len=0,eof=Eof}) ->
  T#tmp{eof=Eof+Size,bbs=[{Key,Eof}],len=1,min=Key,max=Key};
boff_f(#blob{key=Key,size=Size},T = #tmp{eof=Eof,len=Len,bbs=BBs})->
  T#tmp{eof=Eof+Size,bbs=BBs++[{Key,Eof}],len=Len+1,max=Key}.

leaf_disk_format(T) ->
  term_to_binary({T#tmp.len,T#tmp.bbs}).

mk_node(Nodes,Eof) ->
  T = lists:foldl(fun noff_f/2,#tmp{eof=Eof},Nodes),
  Bin = int_disk_format(T),
  #node{length=T#tmp.len,
        size=byte_size(Bin),
        min_key=T#tmp.min,
        max_key=T#tmp.max,
        pos=T#tmp.eof,
        zero_pos=T#tmp.zp,
        bin=Bin}.

noff_f(#node{min_key=M,size=Size},T = #tmp{len=0,eof=Eof})->
  T#tmp{eof=Eof+Size,zp=Eof,bbs=[],len=1,min=M,max=M};
noff_f(#node{min_key=Min,max_key=Max,size=Size},T)->
  #tmp{eof=Eof,len=Len,bbs=BBs} = T,
  T#tmp{eof=Eof+Size,bbs=BBs++[{Min,Eof}],len=Len+1,max=Max}.

int_disk_format(T) ->
  term_to_binary({T#tmp.len,T#tmp.zp,T#tmp.min,T#tmp.max,T#tmp.bbs}).
