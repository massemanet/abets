%% -*- mode: erlang; erlang-indent-level: 2 -*-
%%% Created : 25 Feb 2011 by mats cronqvist <masse@klarna.com>

%% @doc
%% @end

-module('abets').
-author('mats cronqvist').

-export([handle_call/3,
         init/1,
         terminate/2]).

-export([new/1, new/2,
         open/1,
         close/1,
         destroy/1,
         decompose/1, decompose/2,
         insert/3,
         delete/2,
         lookup/2,
         bulk/2, bulk/3,
         first/1,
         last/1,
         next/2]).

-define(SIZE, 4).

-record(state,
        {len=?SIZE,
         len2=?SIZE*2,
         eof=0,
         block_size=2621,
         name,
         fd,
         mode,
         max_key,
         cache=[],
         blobs=[],
         nodes=[[]]}).

-record(header,
        {bin,
         pos,
         size,
         preamble}).

-record(blob,
        {key,
         data,
         pos,
         size,
         bin}).

-record(node,
        {type,
         pos,
         max_key,
         size=0,
         recs=[],
         bin}).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% the api

new(Tab) ->
  new(Tab, []).

new(Tab, Opts) ->
  case proplists:get_value(bulk, Opts) of
    true -> do_new(Tab, bulk);
    _    -> do_new(Tab, create)
  end.

open(Tab) ->
  do_new(Tab, normal).

insert(Tab, Key, Val) ->
  call(Tab, {insert, Key, Val}).

bulk(Tab, commit) ->
  call(Tab, {bulk, commit}).

bulk(Tab, Key, Val) ->
  call(Tab, {bulk, Key, Val}).

delete(Tab, Key) ->
  call(Tab, {delete, Key}).

lookup(Tab, Key) ->
  case call(Tab, {lookup, Key}) of
    {Res} -> Res;
    Error -> exit(Error)
  end.

first(Tab) ->
  call(Tab, {first}).

last(Tab) ->
  call(Tab, {last}).

next(Tab, Key) ->
  call(Tab, {next, Key}).

destroy(Tab) ->
  call(Tab, destroy).

close(Tab) ->
  call(Tab, close).

decompose(Tab) -> decompose(Tab, 0).

decompose(Tab, N) when is_integer(N), 0 =< N ->
  catch open(Tab),
  call(Tab, {decompose, N}).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

call(Tab, What) ->
  gen_server:call(assert(Tab), What).

assert(Tab) ->
  case whereis(RegName = regname(Tab)) of
    undefined -> exit({no_such_table, Tab});
    _         -> RegName
  end.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% gen_server callbacks

init([OpenMode, Name]) ->
  {ok, do_open(OpenMode, #state{name=Name})}.

terminate(normal, []) ->
  ok;
terminate(normal, Filename) ->
  file:delete(Filename),
  ok;
terminate(What, _State) ->
  error_logger:error_report(What).

handle_call(close, _From, _State) ->
  {stop, normal, ok, []};
handle_call(destroy, _From, State) ->
  {stop, normal, ok, filename(State#state.name)};
handle_call(What, _From, OldState) ->
  {Reply, State} = safer(What, OldState),
  {reply, Reply, State}.

safer(What, State) ->
  try do_safer(What, State)
  catch C:R -> {{C, R, erlang:get_stacktrace()}, State}
  end.

do_safer({insert, Key, Val}, State) -> {ok, do_insert(Key, Val, State)};
do_safer({lookup, Key}, State)      -> {do_lookup(Key, State), State};
do_safer({next, Key}, State)        -> {do_next(Key, State), State};
do_safer({delete, Key}, State)      -> {do_delete(Key, State), State};
do_safer({first}, State)            -> {do_first(State), State};
do_safer({last}, State)             -> {do_last(State), State};
do_safer({bulk, Key, Val}, State)   -> {ok, do_bulk(insert, Key, Val, State)};
do_safer({bulk, commit}, State)     -> {ok, do_bulk(commit, '', '', State)};
do_safer({decompose, N}, State)     -> {do_decompose(N, State), State}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
do_new(Tab, How) ->
  try assert(Tab),
       exit({already_exists, Tab})
  catch _:{no_such_table, Tab} ->
      gen_server:start({local, regname(Tab)}, ?MODULE, [How, Tab], [])
  end.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% B+tree logic

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
do_decompose(N, State) ->
  decomp(State, N, read_blob_bw(eof, State), []).

decomp(State, N, Rec, O)  ->
  Pos = get_pos(Rec),
  case N =:= 0 orelse Pos =:= 0 of
    true -> [{Pos, Rec}|O];
    false-> decomp(State, N-1, read_blob_bw(Pos, State), [{Pos, Rec}|O])
  end.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
do_first(State) ->
  Root = #node{type=root} = read_blob_bw(eof, State),
  get_min(Root).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
do_last(State) ->
  Root = #node{type=root} = read_blob_bw(eof, State),
  get_max(Root).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
do_insert(Key, Val, S) ->
  R = #node{type=root} = read_blob_bw(eof, S),
  K = max(min(Key, get_max(R, Key)), get_min(R, Key)),
  Nodes = find_nodes(K, R, [], S),
  Blob = mk_blob(Key, Val, S#state.eof),
  NewLeaves = add_blob_to_leaf(S, Blob, hd(Nodes)),
  flush_cache(
    chk_nods(NewLeaves, S#state{cache=[Blob],
                                nodes=Nodes,
                                max_key=max(get_max(R, Key), Key),
                                eof=S#state.eof+Blob#blob.size})).

add_blob_to_leaf(#state{len=Len, eof=Eof}, Blob, #node{type=leaf, recs=Rs}) ->
  case Len < length(Recs = lists:sort([{Blob#blob.key, Blob#blob.pos}|Rs])) of
    true ->
      {R1s, R2s} = lists:split(Len div 2, Recs),
      L1=mk_leaf(R1s, Eof+Blob#blob.size),
      L2=mk_leaf(R2s, Eof+Blob#blob.size+L1#node.size),
      [L1, L2];
    false->
      [mk_leaf(Recs, Eof+Blob#blob.size)]
  end.

chk_nods([Root], S = #state{nodes=[_], cache=Cache}) ->
  {NewEof, [NewRoot]} = move_pointers([Root], S),
  S#state{cache=Cache++[re_node(NewRoot, S)],
          nodes=[],
          eof=NewEof};
chk_nods(Is=[_, _], S = #state{nodes=[_], cache=Cache, max_key=Max}) ->
  {NewEof, NewIs} = move_pointers(Is, S),
  Recs = [{get_min(I), I#node.pos} || I <- NewIs],
  Root = mk_root(Max, Recs, 0),
  chk_nods([Root], S#state{cache=Cache++NewIs,
                           eof=NewEof});
chk_nods(Kids, S = #state{cache=Cache, nodes=[Kid, Dad|Grands]}) ->
  {NewEof, NewKids} = move_pointers(Kids, S),
  Dads = replace_node(Kid, NewKids, Dad, S),
  chk_nods(Dads, S#state{cache=Cache++NewKids,
                         nodes=[Dad|Grands],
                         eof=NewEof}).

replace_node(Kid, [NewKid], Dad, S) ->
  [re_node(replace_rec(Kid, NewKid, Dad), S)];
replace_node(Kid, [Kid1, Kid2], OldDad, S = #state{len=Len}) ->
  [Dad] = replace_node(Kid, [Kid1], OldDad, S),
  Recs = lists:sort([{get_min(Kid2), Kid2#node.pos}|Dad#node.recs]),
  case Len =< get_length(Dad) of
    true ->
      {Rs1, Rs2} = lists:split(length(Recs) div 2, Recs),
      [mk_internal(Rs1, 0),
       mk_internal(Rs2, 0)];
    false->
      [re_node(Dad#node{recs=Recs}, S)]
  end.

re_node(#node{type=internal, recs=Rs, pos=P}, _) ->
  mk_internal(Rs, P);
re_node(#node{type=root, max_key=Max, recs=Rs, pos=P}, #state{max_key=Mx}) ->
  mk_root(max(Mx, Max), Rs, P).

replace_rec(#node{recs=[]}, #node{recs=[{K, _}|_], pos=Pos}, N=#node{recs=[]}) ->
  N#node{recs=[{K, Pos}]};
replace_rec(#node{recs=[{K0, _}|_]}, #node{recs=[{K1, _}|_], pos=Pos}, N) ->
  N#node{recs=[maybe_replace_rec(K0, {K1, Pos}, {K, P})||{K, P}<-N#node.recs]}.

maybe_replace_rec(K, NewRec, {K, _}) -> NewRec;
maybe_replace_rec(_, _, OldRec) -> OldRec.

move_pointers(Nodes, #state{eof=Eof}) ->
  lists:foldl(fun mp_fun/2, {Eof, []}, Nodes).

mp_fun(N = #node{size=Size}, {Eof, Nodes}) ->
  {Eof+Size, Nodes++[N#node{pos=Eof}]}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
do_delete(Key, State) ->
  try
    deleter(Key, State)
  catch
    _:R -> {not_found, Key, R, erlang:get_stacktrace()}
  end.

deleter(Key, S) ->
  R = #node{type=root} = read_blob_bw(eof, S),
  K = max(min(Key, get_max(R, Key)), get_min(R, Key)),
  Nodes = find_nodes(K, R, [], S),
  flush_cache(
    chk_nods([nullify(Key, hd(Nodes))],
             S#state{cache=[],
                     nodes=Nodes,
                     max_key=max(get_max(R, Key), Key)})).

nullify(Key, Leaf = #node{recs=Recs}) ->
  Leaf#node{recs = nlf(Key, Recs)}.

nlf(Key, [{Key, _}|R]) -> [{Key, 0}|R];
nlf(Key, [I|R])        -> [I|nlf(Key, R)].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
do_lookup(Key, State) ->
  try
    [[{Key, Pos}|_]|_] = leftrecs(Key, State),
    #blob{data=Data} = read_blob_fw(Pos, State),
    {Data}
  catch
    _:R -> {not_found, Key, R}
  end.

do_next(Key, State) ->
  try
    case leftrecs(Key, State) of
      [[{K, Pos}|_]|_] ->
        #blob{data=Data} = read_blob_fw(Pos, State),
        {K, Data};
      [[]|KVs] ->
        exit({backtrack, KVs})
    end
  catch
    _:R -> {not_found, Key, R}
  end.

leftrecs(Key, State) ->
  leftrecs(Key, read_blob_bw(eof, State), [], State).

leftrecs(Key, #node{type=leaf, recs=Recs}, O, _) ->
  [lists:dropwhile(fun({K, _}) -> K < Key end, Recs)|O];
leftrecs(_, #node{type=root, recs=[]}, [], _) ->
  [[]];
leftrecs(Key, #node{recs=Recs}, O, State) ->
  [{_, Pos}|_] = LeftRecs = dropwhile(Key, Recs),
  leftrecs(Key, read_blob_fw(Pos, State), [LeftRecs|O], State).

dropwhile(_, [_] = KVs) -> KVs;
dropwhile(Key, [_, {K1, _}|_] = KVs) when Key < K1 -> KVs;
dropwhile(Key, [_|KVs]) -> dropwhile(Key, KVs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
do_bulk(commit, _, _, State)->
  finalize(State);
do_bulk(insert, Key, Val, State)->
  add_blob(Key, Val, State).

add_blob(Key, Val, S = #state{blobs=Blobs}) ->
  case S#state.len2 =< length(Blobs) of
    true ->
      {BlobsH, BlobsT} = lists:split(S#state.len, Blobs),
      NewLeaf = mk_leaf_bulk(BlobsH, S#state.eof),
      flush_cache(
        check_nodes(
          S#state{nodes=add_leaf(NewLeaf, S),
                  cache=BlobsH++[NewLeaf],
                  max_key=max(S#state.max_key, Key),
                  eof=NewLeaf#node.pos+NewLeaf#node.size,
                  blobs=BlobsT++[mk_blob(Key, Val, 0)]}));
    false->
      S#state{blobs=Blobs++[mk_blob(Key, Val, 0)],
              max_key=max(S#state.max_key, Key)}
  end.

add_leaf(Leaf, #state{nodes=[Leaves|Ints]}) ->
  [Leaves++[Leaf]|Ints].

check_nodes(S = #state{nodes=Nodes}) ->
  {NewNodes, NewCache, NewEof} = chk_nodes(Nodes, S),
  S#state{nodes=NewNodes,
          cache=S#state.cache++NewCache,
          eof=NewEof}.

chk_nodes(Nodes, #state{len=S, len2=S2, eof=Eof}) ->
  chk_nodes(Nodes, {[], [], Eof}, {S, S2}).

chk_nodes([], O, _)         -> O;
chk_nodes([N0s|Nss], {Ns, Cache, Eof}, C={S, S2}) ->
  case S2 < length(N0s) of
    true ->
      {NodesH, NodesT} = lists:split(S, N0s),
      Node = mk_node_bulk(NodesH, Eof),
      NewEof = Node#node.pos+Node#node.size,
      chk_nodes(add_node(Node, Nss), {Ns++[NodesT], Cache++[Node], NewEof}, C);
    false->
      {Ns++[N0s|Nss], Cache, Eof}
  end.

add_node(N, []) -> [[N]];
add_node(N, [Ns|NT]) -> [Ns++[N]|NT].

finalize(S = #state{cache=[], blobs=[], nodes=[[]]}) ->
  Root = mk_root_bulk([], [], S#state.eof),
  NewEof = Root#node.pos+Root#node.size,
  flush_cache(S#state{eof=NewEof, cache=[Root]});
finalize(S0 = #state{cache=[], blobs=Blobs}) ->
  case length(Blobs) =< S0#state.len of
    true ->
      Leaf = mk_leaf_bulk(Blobs, S0#state.eof),
      S2 =
        check_nodes(S0#state{nodes=add_leaf(Leaf, S0),
                             cache=Blobs++[Leaf],
                             eof=Leaf#node.pos+Leaf#node.size,
                             mode=normal,
                             blobs=[]});
    false->
      {Blobs1, Blobs2} = lists:split(length(Blobs) div 2, Blobs),
      Leaf1 = mk_leaf_bulk(Blobs1, S0#state.eof),
      S1 =
        check_nodes(S0#state{nodes=add_leaf(Leaf1, S0),
                             cache=Blobs1++[Leaf1],
                             eof=Leaf1#node.pos+Leaf1#node.size,
                             blobs=Blobs2}),
      Leaf2 = mk_leaf_bulk(Blobs2, S1#state.eof),
      S2 =
        check_nodes(S1#state{nodes=add_leaf(Leaf2, S1),
                             cache=S1#state.cache++Blobs2++[Leaf2],
                             eof=Leaf2#node.pos+Leaf2#node.size,
                             mode=normal,
                             blobs=[]})
  end,
  flush_cache(finalize_nodes(S2)).

finalize_nodes(S = #state{eof=Eof, cache=Cache, nodes=[Ns]}) ->
  case length(Ns) =< S#state.len of
    true ->
      Root = mk_root_bulk(Ns, S#state.max_key, Eof),
      NewEof = Root#node.pos+Root#node.size,
      S#state{eof=NewEof, cache=Cache++[Root], nodes=[]};
    false->
      {N1s, N2s} = lists:split(length(Ns) div 2, Ns),
      Node1 = mk_node_bulk(N1s, Eof),
      NewEof1 = Node1#node.pos+Node1#node.size,
      Node2 = mk_node_bulk(N2s, NewEof1),
      NewEof2 = Node2#node.pos+Node2#node.size,
      finalize_nodes(S#state{cache=Cache++[Node1, Node2],
                             nodes=[[Node1, Node2]],
                             eof=NewEof2})
  end;
finalize_nodes(S = #state{eof=Eof, cache=Cache, nodes=[NHs|NTs]}) ->
  case length(NHs) =< S#state.len of
    true ->
      Node = mk_node_bulk(NHs, Eof),
      NewEof = Node#node.pos+Node#node.size,
      finalize_nodes(S#state{cache=Cache++[Node],
                             nodes=add_node(Node, NTs),
                             eof=NewEof});
    false->
      {NH1s, NH2s} = lists:split(length(NHs) div 2, NHs),
      Node1 = mk_node_bulk(NH1s, Eof),
      NewEof1 = Node1#node.pos+Node1#node.size,
      Node2 = mk_node_bulk(NH2s, NewEof1),
      NewEof2 = Node2#node.pos+Node2#node.size,
      finalize_nodes(S#state{cache=Cache++[Node1, Node2],
                             nodes=add_node(Node2, add_node(Node1, NTs)),
                             eof=NewEof2})
  end.

mk_root_bulk(Nodes, Max, Pos) ->
  Recs = [{Min, Ps} || #node{pos=Ps, recs=[{Min, _}|_]} <- Nodes],
  mk_root(Max, Recs, Pos).

mk_node_bulk(Nodes, Pos) ->
  Recs = [{Min, Ps} || #node{pos=Ps, recs=[{Min, _}|_]} <- Nodes],
  mk_internal(Recs, Pos).

mk_leaf_bulk(Blobs, Eof) ->
  {EOF, Recs} = lists:foldl(fun boff_f/2, {Eof, []}, Blobs),
  mk_leaf(Recs, EOF).

boff_f(#blob{key=Key, size=Size}, {Eof, Recs})->
  {Eof+Size, Recs++[{Key, Eof}]}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% return a list of parent nodes, leaf first, root last

find_nodes(_, N = #node{type=leaf}, O, _) ->
  [N|O];
find_nodes(Key, N = #node{type=root, recs=[]}, [], _) ->
  [mk_leaf([], 0), N#node{max_key=Key}];
find_nodes(Key, N = #node{recs=Recs}, O, State) ->
  find_nodes(Key, read_blob_fw(pointer(Key, Recs), State), [N|O], State).

pointer(Key, [{K0, P0}, {K1, P1}|Recs]) ->
  case K0 =< Key andalso Key < K1 of
    true -> P0;
    false-> pointer(Key, [{K1, P1}|Recs])
  end;
pointer(_, [{_, P0}]) ->
  P0.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% file ops

-define(TYPE_BYTES, 1).
-define(SIZE_BYTES, 4).
-define(SIZE_BITS, 32).
-define(PAD_BYTES, (?SIZE_BYTES+?TYPE_BYTES)).

-define(TYPE_LEAF_NODE , <<1>>).
-define(TYPE_INT_NODE  , <<2>>).
-define(TYPE_ROOT_NODE , <<3>>).
-define(TYPE_BLOB      , <<4>>).
-define(TYPE_HEADER    , <<5>>).
-define(TYPE_TERM      , 6).
-define(TYPE_BIN       , 7).

do_open(OpenMode, State) ->
  maybe_delete(OpenMode, State),
  {ok, FD} = file:open(filename(State#state.name), [read, append, binary, raw]),
  case eof(FD) of
    0 ->
      write(FD, [H = mk_header(State)]),
      flush_cache(
        finalize(State#state{
                   mode=fill_mode(OpenMode),
                   fd=FD,
                   eof=H#header.size}));
    Eof ->
      State#state{mode=fill_mode(OpenMode),
                  eof=Eof,
                  fd=FD}
  end.

fill_mode(bulk) -> bulk;
fill_mode(_) -> normal.

maybe_delete(normal, _) -> ok;
maybe_delete(_, #state{name=Name}) -> file:delete(filename(Name)).

flush_cache(S = #state{fd=FD, cache=Cache}) ->
  write(FD, Cache),
  S#state{cache=[]}.

filename(Tab) ->
  atom_to_list(Tab).

regname(Tab) ->
  list_to_atom("abets_"++atom_to_list(Tab)).

pad_size() ->
  ?PAD_BYTES+?PAD_BYTES.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% disk format

read_blob_bw(eof, State) -> read_blob_bw(eof(State#state.fd), State);
read_blob_bw(End, #state{fd=FD, block_size=BSIZE}) ->
  {Ptr, Size, Bin} = read(FD, max(0, End-BSIZE), End),
  [exit({bin_error1, {Size}}) || Size < ?TYPE_BYTES+?SIZE_BYTES],
  Off = Size-?TYPE_BYTES-?SIZE_BYTES,
  <<_:Off/binary, Type:?TYPE_BYTES/binary, BS:?SIZE_BITS/integer>> = Bin,
  [exit({bin_error2, {Size, BS}}) || Size < BS+(?PAD_BYTES+?PAD_BYTES)],
  Of = Size-BS-(?PAD_BYTES+?PAD_BYTES),
  <<_:Of/binary, _:?PAD_BYTES/binary, BT:BS/binary, _:?PAD_BYTES/binary>> = Bin,
  [exit({bin_error3, {Size, BS}}) || Ptr+Of =/= End-(BS+?PAD_BYTES+?PAD_BYTES)],
  unwrap(Type, BT, Ptr+Of).


read_blob_fw(Beg, #state{fd=FD, block_size=BSIZE}) ->
  {Beg, Size, Bin} = read(FD, Beg, Beg+BSIZE),
  [exit({blob_error, {Size}}) || Size < ?PAD_BYTES],
  <<Sz:?SIZE_BITS/integer, Type:?TYPE_BYTES/binary, _/binary>> = Bin,
  [exit({blob_error, {Size, Sz}}) || Size < Sz+?PAD_BYTES],
  <<_:?PAD_BYTES/binary, BT:Sz/binary, _/binary>> = Bin,
  unwrap(Type, BT, Beg).

write(FD, IOlist) ->
  ok = file:write(FD, [wrap(E) || E <- IOlist]),
%%%  file:sync(FD),
  ok.

read(FD, Beg, End) ->
  [exit({read_error, {Beg}}) || Beg < 0],
  [exit({read_error, {Beg, End}}) || End < Beg],
  {ok, Bin} = file:pread(FD, Beg, End-Beg),
  Size = byte_size(Bin),
  {Beg, Size, Bin}.

wrap(Rec) ->
  Type = type(Rec),
  Binary = get_bin(Rec),
  BS = byte_size(Binary),
  Sz = <<BS:?SIZE_BITS/integer>>,
  [Sz, Type, Binary, Type, Sz].

unwrap(Type, B, Pos) ->
  case Type of
    ?TYPE_LEAF_NODE -> from_disk_format_leaf(B, Pos);
    ?TYPE_INT_NODE  -> from_disk_format_internal(B, Pos);
    ?TYPE_ROOT_NODE -> from_disk_format_root(B, Pos);
    ?TYPE_BLOB      -> from_disk_format_blob(B, Pos);
    ?TYPE_HEADER    -> from_disk_format_header(B, Pos)
  end.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
from_disk_format_blob(<<?TYPE_BIN:8/integer, Bin/binary>>, Pos) ->
  #blob{data=Bin, pos=Pos};
from_disk_format_blob(<<?TYPE_TERM:8/integer, Bin/binary>>, Pos) ->
  #blob{data=binary_to_term(Bin), pos=Pos}.

mk_blob(Key, Val, Pos) ->
  Bin = to_disk_format_blob(Val),
  #blob{key=Key,
        data=Val,
        pos=Pos,
        bin=Bin,
        size=byte_size(Bin)+pad_size()}.

to_disk_format_blob(Bin) when is_binary(Bin) ->
  <<?TYPE_BIN:8/integer, Bin/binary>>;
to_disk_format_blob(Val) ->
  Bin=to_binary(Val),
  <<?TYPE_TERM:8/integer, Bin/binary>>.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
from_disk_format_leaf(Bin, Pos) ->
  Recs = binary_to_term(Bin),
  mk_leaf(Recs, Pos).

mk_leaf(Recs, Pos) ->
  Bin = to_disk_format_leaf(Recs),
  #node{type=leaf,
        pos=Pos,
        max_key=case Recs of []->[];_->element(1, hd(lists:reverse(Recs)))end,
        recs=Recs,
        bin=Bin,
        size=byte_size(Bin)+pad_size()}.

to_disk_format_leaf(Recs) ->
  to_binary(Recs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
from_disk_format_internal(Bin, Pos) ->
  {Recs} = binary_to_term(Bin),
  mk_internal(Recs, Pos).

mk_internal(Recs, Pos) ->
  Bin = to_disk_format_internal(Recs),
  #node{type=internal,
        pos=Pos,
        size=byte_size(Bin)+pad_size(),
        bin=Bin,
        recs=Recs}.

to_disk_format_internal(Recs) ->
  to_binary({Recs}).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
from_disk_format_root(Bin, Pos) ->
  {Max, Recs} = binary_to_term(Bin),
  mk_root(Max, Recs, Pos).

mk_root(Max, Recs, Pos) ->
  Bin = to_disk_format_root(Max, Recs),
  #node{type=root,
        pos=Pos,
        max_key=Max,
        size=byte_size(Bin)+pad_size(),
        bin=Bin,
        recs=Recs}.

to_disk_format_root(Max, Recs) ->
  to_binary({Max, Recs}).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
from_disk_format_header(Bin, Pos) ->
  Preamble = binary_to_term(Bin),
  mk_header(Preamble, Pos).

mk_header(#state{}) ->
  mk_header("ABETS v1", 0).

mk_header(Preamble, Pos) ->
  Bin = to_disk_format_header(Preamble),
  #header{preamble=Preamble,
          pos=Pos,
          bin=Bin,
          size=byte_size(Bin)+pad_size()}.

to_disk_format_header(Preamble) ->
  term_to_binary(Preamble).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
to_binary(Term) ->
  term_to_binary(Term, [{compressed, 3}, {minor_version, 1}]).

eof(FD) ->
  {ok, Pos} = file:position(FD, eof),
  Pos.

get_min(N, K) ->
  try get_min(N)
  catch _:_ -> K
  end.

get_min(#node{recs=[{Min, _}|_]}) -> Min.

get_max(N, K) ->
  try get_max(N)
  catch _:_ -> K
  end.

get_max(#node{recs=[_|_], max_key=Max}) -> Max.

get_length(#node{type=leaf, recs=Recs})     -> length(Recs);
get_length(#node{type=internal, recs=Recs}) -> length(Recs)+1;
get_length(#node{type=root, recs=Recs})     -> length(Recs)+1.

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
