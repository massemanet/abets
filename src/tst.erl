%% -*- mode: erlang; erlang-indent-level: 2 -*-
%%% Created : 25 Feb 2011 by mats cronqvist <masse@klarna.com>

%% @doc
%% @end

-module('tst').
-author('mats cronqvist').

-export([tree/1,
         unit/0, unit/1
         , wunit/0, wunit/1
         , unit_bulk_small/0
         , unit_bulk/0]).

-export([handle_call/3
         , init/1
         , terminate/2]).

-export([new/1, new/2
         , open/1
         , close/1
         , destroy/1
         , decompose/1, decompose/2
         , insert/3
         , delete/2
         , lookup/2
         , bulk/2, bulk/3
         , first/1
         , last/1
         , next/2]).

-define(SIZE,4).

-record(state,
        {len=?SIZE,
         len2=?SIZE*2,
         eof=0,
         block_size=2621,
         name,
         fd,
         mode,
         cache=[],
         blobs=[],
         nodes=[[]]}).

-record(header,
        {bin,
         pos,
         size,
         data}).

-record(blob,
        {key,
         data,
         pos,
         size,
         bin}).

-record(node,
        {type,
         pos,
         size=0,
         length=0,
         min_key,
         max_key,
         zero_pos=0,
         recs=[],
         bin}).

tree(L) ->
  finalize(lists:foldl(fun add_blob_f/2,#state{},lists:seq(1,L))).

add_blob_f(N,S)->
  add_blob({k,N},{v,N},S).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% the api

new(Tab) ->
  new(Tab,[]).

new(Tab,Opts) ->
  case proplists:get_value(bulk,Opts) of
    true -> do_new(Tab,bulk);
    _    -> do_new(Tab,create)
  end.

open(Tab) ->
  do_new(Tab,normal).

insert(Tab,Key,Val) ->
  call(Tab,{insert,Key,Val}).

bulk(Tab,commit) ->
  call(Tab,{bulk,commit}).

bulk(Tab,Key,Val) ->
  call(Tab,{bulk,Key,Val}).

delete(Tab, Key) ->
  call(Tab,{delete,Key}).

lookup(Tab, Key) ->
  case call(Tab,{lookup,Key}) of
    {Res} -> Res;
    Error -> exit(Error)
  end.

first(Tab) ->
  call(Tab,{first}).

last(Tab) ->
  call(Tab,{last}).

next(Tab, Key) ->
  call(Tab,{next,Key}).

destroy(Tab) ->
  call(Tab,destroy).

close(Tab) ->
  call(Tab,close).

decompose(Tab) -> decompose(Tab,0).

decompose(Tab,N) when is_integer(N), 0 =< N ->
  catch open(Tab),
  call(Tab,{decompose,N}).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

call(Tab,What) ->
  gen_server:call(assert(Tab),What).

assert(Tab) ->
  case whereis(RegName = regname(Tab)) of
    undefined -> exit({no_such_table,Tab});
    _         -> RegName
  end.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% gen_server callbacks

init([OpenMode,Name]) ->
  {ok,do_open(OpenMode,#state{name=Name})}.

terminate(normal,[]) ->
  ok;
terminate(normal,Filename) ->
  file:delete(Filename),
  ok;
terminate(What,_State) ->
  error_logger:error_report(What).

handle_call(close,_From,_State) ->
  {stop,normal,ok,[]};
handle_call(destroy,_From,State) ->
  {stop,normal,ok,filename(State#state.name)};
handle_call(What,_From,OldState) ->
  {Reply,State} = safer(What,OldState),
  {reply,Reply,State}.

safer(What,State) ->
  try do_safer(What,State)
  catch C:R -> exit({C,R,erlang:get_stacktrace()})
  end.

do_safer({first},State)          -> {do_first(State),State};
do_safer({last},State)           -> {do_last(State),State};
do_safer({insert,Key,Val},State) -> {do_insert(Key,Val,State),State};
do_safer({lookup,Key},State)     -> {do_lookup(Key,State),State};
do_safer({bulk,Key,Val},State)   -> do_bulk(insert,Key,Val,State);
do_safer({bulk,commit},State)    -> do_bulk(commit,'','',State);
do_safer({decompose,N},State)    -> {do_decompose(N,State),State}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
do_new(Tab,How) ->
  try assert(Tab),
      exit({already_exists,Tab})
  catch _:{no_such_table,Tab} ->
      gen_server:start({local,regname(Tab)},?MODULE,[How,Tab],[])
  end.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% B+tree logic

%%%
do_decompose(N,State) ->
  decomp(State,N,read_blob_bw(eof,State),[]).

decomp(State,N,Rec,O)  ->
  Pos = get_pos(Rec),
  case N =:= 0 orelse Pos =:= 0 of
    true -> [{Pos,Rec}|O];
    false-> decomp(State,N-1,read_blob_bw(Pos,State),[{Pos,Rec}|O])
  end.

do_first(State) ->
  #node{type=root,min_key=First} = read_blob_bw(eof,State),
  First.

do_last(State) ->
  #node{type=root,max_key=Last} = read_blob_bw(eof,State),
  Last.

do_insert(Key,Val,S) ->
  R = #node{type=root} = read_blob_bw(eof,S),
  K = erlang:max(erlang:min(Key,R#node.max_key),R#node.min_key),
  Nodes = find_nodes(K,R,[],S),
  Blob = (mk_blob(Key,Val))#blob{pos=S#state.eof},
  NewLeaves = add_blob_to_leaf(S,Blob,hd(Nodes)),
  chk_nods(NewLeaves,S#state{cache=[Blob],
                             nodes=Nodes,
                             eof=S#state.eof+Blob#blob.size}).

add_blob_to_leaf(#state{len=Len,eof=Eof},Blob,#node{type=leaf,recs=Rs}) ->
 case Len =< length(Recs = lists:sort([{Blob#blob.key,Blob#blob.pos}|Rs])) of
   true ->
     [mk_leaf(Recs,Eof+Blob#blob.size)];
   false->
     {R1s,R2s} = lists:split(Len div 2,Recs),
     L1=mk_leaf(R1s,Eof+Blob#blob.size),
     L2=mk_leaf(R2s,Eof+Blob#blob.size+L1#node.size),
     [L1,L2]
 end.

chk_nods([Root],S = #state{nodes=[_],eof=Eof,cache=Cache}) ->
  S#state{cache=Cache++[Root#node{pos=Eof}],
          nodes=[],
          eof=Eof+Root#node.size};
chk_nods(Kids,S = #state{cache=Cache,nodes=[Kid,Dad|Grands]}) ->
  Dads = replace_node(Kid,Kids,Dad,S),
  {NewEof,NewKids} = move_pointers(Kids,S),
  chk_nods(Dads,S#state{cache=Cache++NewKids,
                        nodes=[Dad|Grands],
                        eof=NewEof}).

replace_node(Kid,[NewKid],Dad,_) ->
  case is_smallest(Kid,Dad) of
    true -> [Dad#node{zero_pos=NewKid#node.pos,min_key=min_key(NewKid,Dad)}];
    false-> [replace_rec(Kid,NewKid,Dad)]
  end;
replace_node(Kid,[Kid1,Kid2],OldDad,S = #state{len=Len}) ->
  Dad = replace_node(Kid,[Kid1],OldDad,S),
  Recs = [{Kid2#node.min_key,Kid2#node.pos}|Dad#node.recs],
  case Len =< Dad#node.length of
    true -> 
      Rs = lists:sort([{Dad#node.min_key,Dad#node.zero_pos}|Recs]),
      {[{M1,Z1}|Rs1],[{M2,Z2}|Rs2]} = lists:split(length(Rs)+1 div 2,Rs),
      [mk_internal(Z1,M1,Rs1,0),
       mk_internal(Z2,M2,Rs2,0)];
    false->
      [Dad#node{recs=Recs,length=length(Recs)}]
  end.

is_smallest(#node{min_key=Min0},#node{min_key=Min1}) ->
  Min0 =:= Min1.

replace_rec(#node{min_key=K0},#node{min_key=K1,pos=Pos},N) ->
  N#node{recs=[maybe_replace_rec(K0,{K1,Pos},{K,P})||{K,P}<-N#node.recs]}.

maybe_replace_rec(K,NewRec,{K,_}) -> NewRec;
maybe_replace_rec(_,_,OldRec) -> OldRec.

min_key(#node{min_key=K1},#node{min_key=K2}) -> erlang:min(K1,K2).

move_pointers(Nodes,#state{eof=Eof}) ->
  lists:foldl(fun mp_fun/2,{Eof,[]},Nodes).

mp_fun(N = #node{size=Size},{Eof,Nodes}) ->
  {Eof+Size,Nodes++[N#node{pos=Eof}]}.

do_lookup(Key,State) ->
  try
    [Leaf|_] = find_nodes(Key,State),
    #blob{data=Data} = read_blob(Key,Leaf,State),
    {Data}
  catch
    _:R -> {not_found,Key,R}
  end.

read_blob(Key,#node{type=leaf,recs=Recs},State) ->
  {value,{Key,Pos}} = lists:keysearch(Key,1,Recs),
  read_blob_fw(Pos,State).

find_nodes(Key,State) ->
  find_nodes(Key,read_blob_bw(eof,State),[],State).

find_nodes(_,N = #node{type=leaf},O,_) ->
  [N|O];
find_nodes(Key,N = #node{recs=[]},O,State) ->
  find_nodes(Key,read_blob_fw(N#node.zero_pos,State),[N|O],State);
find_nodes(Key,N = #node{recs=[{K0,_}|_]},O,State) when Key < K0 ->
  find_nodes(Key,read_blob_fw(N#node.zero_pos,State),[N|O],State);
find_nodes(Key,N = #node{recs=Recs},O,State) ->
  find_nodes(Key,read_blob_fw(find(Key,Recs),State),[N|O],State).

find(Key,[{K0,P0},{K1,P1}|Recs]) ->
  case K0 =< Key andalso Key < K1 of
    true -> P0;
    false-> find(Key,[{K1,P1}|Recs])
  end;
find(_,[{_,P0}]) ->
  P0.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


finalize(S0 = #state{cache=[],blobs=Blobs}) ->
  case length(Blobs) =< S0#state.len of
    true ->
      Leaf = mk_leaf_bulk(Blobs,S0#state.eof),
      S2 =
        check_nodes(S0#state{nodes=add_leaf(Leaf,S0),
                             cache=Blobs++[Leaf],
                             eof=Leaf#node.pos+Leaf#node.size,
                             blobs=[]});
    false->
      {Blobs1,Blobs2} = lists:split(length(Blobs) div 2,Blobs),
      Leaf1 = mk_leaf_bulk(Blobs1,S0#state.eof),
      S1 =
        check_nodes(S0#state{nodes=add_leaf(Leaf1,S0),
                             cache=Blobs1++[Leaf1],
                             eof=Leaf1#node.pos+Leaf1#node.size,
                             blobs=Blobs2}),
      Leaf2 = mk_leaf_bulk(Blobs2,S1#state.eof),
      S2 =
        check_nodes(S1#state{nodes=add_leaf(Leaf2,S1),
                             cache=S1#state.cache++Blobs2++[Leaf2],
                             eof=Leaf2#node.pos+Leaf2#node.size,
                             blobs=[]})
  end,
  flush_cache(finalize_nodes(S2)).

finalize_nodes(S = #state{eof=Eof,cache=Cache,nodes=[Ns]}) ->
  case length(Ns) =< S#state.len of
    true ->
      Root = mk_root(Ns,Eof),
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
  case length(NHs) =< S#state.len of
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

do_bulk(commit,_,_,State)->
  {ok,finalize(State)};
do_bulk(insert,Key,Val,State)->
  {ok,add_blob(Key,Val,State)}.

add_blob(Key,Val,S = #state{blobs=Blobs}) ->
  case S#state.len2 =< length(Blobs) of
    true ->
      {BlobsH,BlobsT} = lists:split(S#state.len,Blobs),
      NewLeaf = mk_leaf_bulk(BlobsH,S#state.eof),
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

chk_nodes(Nodes,#state{len=S,len2=S2,eof=Eof}) ->
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

-record(tmp,{eof,recs,len=0,min,max,zp}).

mk_root(Nodes,Eof) ->
  T = lists:foldl(fun noff_f/2,#tmp{},Nodes),
  mk_root(T#tmp.zp,T#tmp.min,T#tmp.max,T#tmp.recs,Eof).

mk_node(Nodes,Pos) ->
  T = lists:foldl(fun noff_f/2,#tmp{},Nodes),
  mk_internal(T#tmp.zp,T#tmp.min,T#tmp.recs,Pos).

noff_f(#node{pos=Pos,min_key=Min,max_key=Max},T = #tmp{len=0})->
  T#tmp{zp=Pos,len=1,min=Min,max=Max,recs=[]};
noff_f(#node{pos=Pos,max_key=Max,min_key=Min},T = #tmp{len=Len,recs=Recs})->
  T#tmp{len=Len+1,max=Max,recs=Recs++[{Min,Pos}]}.

mk_leaf_bulk(Blobs,Eof) ->
  T = lists:foldl(fun boff_f/2,#tmp{eof=Eof},Blobs),
  mk_leaf(T#tmp.recs,T#tmp.eof).

boff_f(#blob{key=Key,size=Size},T = #tmp{len=0,eof=Eof}) ->
  T#tmp{eof=Eof+Size,recs=[{Key,Eof}],len=1,min=Key,max=Key};
boff_f(#blob{key=Key,size=Size},T = #tmp{eof=Eof,len=Len,recs=Recs})->
  T#tmp{eof=Eof+Size,recs=Recs++[{Key,Eof}],len=Len+1,max=Key}.

mk_blob(Key,Val) ->
  Bin = to_disk_format_blob(Val),
  #blob{key=Key,
        data=Val,
        bin=Bin,
        size=byte_size(Bin)+pad_size()}.

mk_header(_State) ->
  Data = "ABETS v1",
  Bin = to_disk_format_header(Data),
  #header{bin = Bin,
          data = Data,
          size=byte_size(Bin)+pad_size()}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% file ops

-define(TYPE_BYTES, 1).
-define(SIZE_BYTES, 4).
-define(SIZE_BITS, 32).
-define(PAD_BYTES,(?SIZE_BYTES+?TYPE_BYTES)).

-define(TYPE_LEAF_NODE , <<1>>).
-define(TYPE_INT_NODE  , <<2>>).
-define(TYPE_ROOT_NODE , <<3>>).
-define(TYPE_BLOB      , <<4>>).
-define(TYPE_HEADER    , <<5>>).
-define(TYPE_TERM      , 6).
-define(TYPE_BIN       , 7).

do_open(OpenMode,State) ->
  maybe_delete(OpenMode,State),
  {ok,FD} = file:open(filename(State#state.name),[read,append,binary,raw]),
  case eof(FD) of
    0 ->
      write(FD,[H = mk_header(State)]),
      Eof = H#header.size;
    Eof ->
      ok
  end,
  State#state{mode=fill_mode(OpenMode),
              eof=Eof,
              fd=FD}.

fill_mode(bulk) -> bulk;
fill_mode(_) -> normal.

maybe_delete(normal,_) -> ok;
maybe_delete(_,#state{name=Name}) -> file:delete(filename(Name)).

flush_cache(S = #state{fd=FD,cache=Cache}) ->
  io:fwrite("FLUSHING:~n~p~n",[S#state.cache]),
  write(FD,Cache),
  S#state{cache=[]}.

filename(Tab) ->
  atom_to_list(Tab).

regname(Tab) ->
  list_to_atom("abets_"++atom_to_list(Tab)).

pad_size() ->
  ?PAD_BYTES+?PAD_BYTES.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% disk format

read_blob_bw(eof,State) -> read_blob_bw(eof(State#state.fd),State);
read_blob_bw(End,#state{fd=FD,block_size=BSIZE}) ->
  {Ptr,Size,Bin} = read(FD,erlang:max(0,End-BSIZE),End),
  [exit({bin_error1,{Size}}) || Size < ?TYPE_BYTES+?SIZE_BYTES],
  Off = Size-?TYPE_BYTES-?SIZE_BYTES,
  <<_:Off/binary,Type:?TYPE_BYTES/binary,BS:?SIZE_BITS/integer>> = Bin,
  [exit({bin_error2,{Size,BS}}) || Size < BS+(?PAD_BYTES+?PAD_BYTES)],
  Of = Size-BS-(?PAD_BYTES+?PAD_BYTES),
  <<_:Of/binary,_:?PAD_BYTES/binary,BT:BS/binary,_:?PAD_BYTES/binary>> = Bin,
  [exit({bin_error3,{Size,BS}}) || Ptr+Of =/= End-(BS+?PAD_BYTES+?PAD_BYTES)],
  unwrap(Type,BT,Ptr+Of).


read_blob_fw(Beg,#state{fd=FD,block_size=BSIZE}) ->
  {Beg,Size,Bin} = read(FD,Beg,Beg+BSIZE),
  [exit({blob_error,{Size}}) || Size < ?PAD_BYTES],
  <<Sz:?SIZE_BITS/integer,Type:?TYPE_BYTES/binary,_/binary>> = Bin,
  [exit({blob_error,{Size,Sz}}) || Size < Sz+?PAD_BYTES],
  <<_:?PAD_BYTES/binary,BT:Sz/binary,_/binary>> = Bin,
  unwrap(Type,BT,Beg).

write(FD,IOlist) ->
  ok = file:write(FD,[wrap(E) || E <- IOlist]),
%  file:sync(FD),
  ok.

read(FD,Beg,End) ->
  [exit({read_error,{Beg}}) || Beg < 0],
  [exit({read_error,{Beg,End}}) || End < Beg],
  {ok,Bin} = file:pread(FD,Beg,End-Beg),
  Size = byte_size(Bin),
  {Beg,Size,Bin}.

wrap(Rec) ->
  Type = type(Rec),
  Binary = get_bin(Rec),
  BS = byte_size(Binary),
  Sz = <<BS:?SIZE_BITS/integer>>,
  [Sz,Type,Binary,Type,Sz].

unwrap(Type,B,Pos) ->
  case Type of
    ?TYPE_LEAF_NODE -> from_disk_format_leaf(B,Pos);
    ?TYPE_INT_NODE  -> from_disk_format_internal(B,Pos);
    ?TYPE_ROOT_NODE -> from_disk_format_root(B,Pos);
    ?TYPE_BLOB      -> from_disk_format_blob(B,Pos);
    ?TYPE_HEADER    -> from_disk_format_header(B,Pos)
  end.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
from_disk_format_blob(<<?TYPE_BIN:8/integer,Bin/binary>>,Pos) ->
  #blob{data=Bin,pos=Pos};
from_disk_format_blob(<<?TYPE_TERM:8/integer,Bin/binary>>,Pos) ->
  #blob{data=binary_to_term(Bin),pos=Pos}.

to_disk_format_blob(Bin) when is_binary(Bin) ->
  <<?TYPE_BIN:8/integer,Bin/binary>>;
to_disk_format_blob(Val) ->
  Bin=to_binary(Val),
  <<?TYPE_TERM:8/integer,Bin/binary>>.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
from_disk_format_leaf(Bin,Pos) ->
  Recs = binary_to_term(Bin),
  mk_leaf(Recs,Pos).

mk_leaf(Recs,Pos) ->
  Bin = to_disk_format_leaf(Recs),
  #node{type=leaf,
        pos=Pos,
        length=length(Recs),
        min_key=element(1,hd(Recs)),
        max_key=element(1,hd(lists:reverse(Recs))),
        recs=Recs,
        bin=Bin,
        size=byte_size(Bin)+pad_size(),
        zero_pos=leaf}.

to_disk_format_leaf(Recs) ->
  to_binary(Recs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
from_disk_format_internal(Bin,Pos) ->
  {Zp,Min,Recs} = binary_to_term(Bin),
  mk_internal(Zp,Min,Recs,Pos).

mk_internal(Zp,Min,Recs,Pos) ->
  Bin = to_disk_format_internal(Zp,Min,Recs),
  #node{type=internal,
        pos=Pos,
        length=length(Recs)+1,
        min_key=Min,
        size=byte_size(Bin)+pad_size(),
        bin=Bin,
        zero_pos=Zp,
        recs=Recs}.

to_disk_format_internal(Zp,Min,Recs) ->
  to_binary({Zp,Min,Recs}).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
from_disk_format_root(Bin,Pos) ->
  {Zp,Min,Max,Recs} = binary_to_term(Bin),
  mk_root(Zp,Min,Max,Recs,Pos).

mk_root(Zp,Min,Max,Recs,Pos) ->
  Bin = to_disk_format_root(Zp,Min,Max,Recs),
  #node{type=root,
        pos=Pos,
        length=length(Recs)+1,
        min_key=Min,
        max_key=Max,
        zero_pos=Zp,
        size=byte_size(Bin)+pad_size(),
        bin=Bin,
        recs=Recs}.

to_disk_format_root(Zp,Min,Max,Recs) ->
  to_binary({Zp,Min,Max,Recs}).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
from_disk_format_header(Bin,Pos) ->
  #header{pos=Pos,
          data=binary_to_term(Bin)}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
to_disk_format_header(Data) ->
  term_to_binary(Data).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
to_binary(Term) ->
  term_to_binary(Term,[{compressed,3},{minor_version,1}]).

eof(FD) ->
  {ok,Pos} = file:position(FD,eof),
  Pos.

get_bin(#header{bin=Bin}) -> Bin;
get_bin(#node{bin=Bin})   -> Bin;
get_bin(#blob{bin=Bin})   -> Bin.

get_pos(#header{pos=Pos}) -> Pos;
get_pos(#node{pos=Pos})   -> Pos;
get_pos(#blob{pos=Pos})   -> Pos.

type(#node{type=leaf})    -> ?TYPE_LEAF_NODE;
type(#node{type=internal})-> ?TYPE_INT_NODE;
type(#node{type=root})    -> ?TYPE_ROOT_NODE;
type(#blob{})             -> ?TYPE_BLOB;
type(#header{})           -> ?TYPE_HEADER.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% ad-hoc unit testing

unit_bulk() ->
  catch destroy(foo),
  new(foo,[bulk]),
  [bulk(foo,N,{mange,N})||N<-[10,11,12,13,14,15,16,17,18,19,20,21,22]],
  bulk(foo,commit).

unit_bulk_small() ->
  catch destroy(foo),
  new(foo,[bulk]),
  [bulk(foo,N,{mange,N})||N<-[10,11,12,13]],
  bulk(foo,commit).

unit() ->
  unit(10000).

unit(N) when is_integer(N) -> unit(shuffle(lists:seq(1,N)));
unit(L) when is_list(L) ->
  catch destroy(foo),
  io:fwrite("length: ~p~n",[length(L)]),
  new(foo),
  [insert(foo,E,{tobbe,E}) || E <- L],
  try length([{tobbe,E}=lookup(foo,E) || E <- L])
  catch _:R -> R
  end.

shuffle(L) ->
  [V||{_,V}<-lists:sort([{random:uniform(),E}||E<-L])].

wunit() -> wunit(10000).

wunit(N) when is_integer(N) -> wunit(shuffle(lists:seq(1,N)));
wunit(L) when is_list(L) ->
  catch destroy(foo),
  new(foo),
  try [wunit(E,L) || E <- L],length(L)
  catch _:R -> R
  after close(foo)
  end.

wunit(E,L) ->
  insert(foo,E,{tobbe,E}),
  Ss = sub(L,E),
  try length([{tobbe,I}=lookup(foo,I) || I <- Ss])
  catch _:R -> exit({R,E,Ss})
  end.

sub([E|_],E) -> [E];
sub([H|T],E) -> [H|sub(T,E)].
