%% -*- mode: erlang; erlang-indent-level: 2 -*-
%%% Created :  6 Apr 2010 by Mats Cronqvist <masse@kreditor.se>

%% @doc
%% @end

-module('abets').
-author('Mats Cronqvist').

-export([unit/0, unit/1
         , wunit/0, wunit/1
         , do_lookup/2
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
         , next/2]).

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
  do_new(Tab,open).

insert(Tab,Key,Val) ->
  call(Tab,{insert,Key,Val}).

bulk(Tab,commit) ->
  call(Tab,{bulk,commit}).

bulk(Tab,Key,Val) ->
  call(Tab,{bulk,Key,Val}).

delete(Tab, Key) ->
  call(Tab,{delete,Key}).

lookup(Tab, Key) ->
  try {Res} = call(Tab,{lookup,Key}),
      Res
  catch _:{badmatch,X} ->
      throw(X)
  end.

first(Tab) ->
  call(Tab,first).

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
%% declarative

-define(ORDER2,4).       %order*2
-define(BLOCK_SIZE,2621).%1048576).%

-define(HEADER,<<"ABETS v1">>).
%% file format looks like
%% [Size,Type,Blob,Type,Size]
-define(TYPE_BYTES, 1).
-define(SIZE_BYTES, 4).
-define(SIZE_BITS, 32).
-define(PAD_BYTES,(?SIZE_BYTES+?TYPE_BYTES)).

-define(TYPE_INTERNAL,<<1>>).
-define(TYPE_LEAF,    <<2>>).
-define(TYPE_BINARY,  <<3>>).
-define(TYPE_TERM,    <<4>>).

-record(rec,
       {key
        , pointer = 0}).

-record(internal,
        {size = 0
         , type = root  %normal|root
         , prog
         , pointer = 0
         , recs = []}).

-record(leaf,
        {size = 0
         , recs = []}).

-record(state,
        {fd
         , bulk_nodes = []
         , name
         , regname
         , filename}).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% gen_server callbacks

init([open,Tab]) ->
  do_init(Tab,do_open(Tab));
init([bulk,Tab]) ->
  do_init(Tab,do_bulk(Tab));
init([create,Tab]) ->
  do_init(Tab,do_create(Tab)).

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
  {stop,normal,ok,State#state.filename};
handle_call(What,_From,OldState) ->
  {Reply,State} = safer(What,OldState),
  {reply,Reply,State}.

safer(What,State) ->
  try do_safer(What,State)
  catch C:R -> exit({C,R,erlang:get_stacktrace()})
  end.

do_safer({lookup,Key},State)     -> {do_lookup(Key,State#state.fd),State};
do_safer({insert,Key,Val},State) -> {do_insert(Key,Val,State),State};
do_safer({bulk,Key,Val},State)   -> do_bulk(Key,Val,State);
do_safer({bulk,commit},State)    -> do_bulk(commit,State);
do_safer({decompose,N},State)    -> {do_decompose(N,State#state.fd),State}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
do_new(Tab,How) ->
  try assert(Tab),
      exit({already_exists,Tab})
  catch _:{no_such_table,Tab} ->
      gen_server:start({local,regname(Tab)},?MODULE,[How,Tab],[])
  end.

do_init(Tab,{FD,[]}) ->
  {ok, #state{name = Tab
              , fd = FD
              , regname = regname(Tab)
              , filename = filename(Tab)}};
do_init(Tab,{FD,Nodes}) ->
  {ok, #state{name = Tab
              , fd = FD
              , regname = regname(Tab)
              , filename = filename(Tab)
              , bulk_nodes=Nodes}}.

filename(Tab) ->
  atom_to_list(Tab).

regname(Tab) ->
  list_to_atom("abets_"++atom_to_list(Tab)).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% B+tree logic

%%%
do_decompose(N,FD) ->
  decomp(FD,N,read_blob_bw(FD,eof),[]).

decomp(_FD,0,{Term,Pos},O) -> [{Pos,Term}|O];
decomp(_FD,_N,{Term,0},O)  -> [{0,Term}|O];
decomp(FD,N,{Term,Pos},O)  ->
  decomp(FD,N-1,read_blob_bw(FD,Pos),[{Pos,Term}|O]).

%%%
do_lookup(Key,FD) ->
  find(FD,Key,read_blob_bw(FD,eof)).

find(FD,Key,{Node,_}) ->
  case Node of
    #internal{pointer=Pointer,recs=Recs} ->
      find(FD,Key,read_blob_fw(FD,new_pos(Key,Recs,Pointer)));
    #leaf{recs=Recs} ->
      case lists:keysearch(Key,2,Recs) of
        {value,#rec{pointer=Pointer}} -> {element(1,read_blob_fw(FD,Pointer))};
        false -> {error,{no_hit,Key}}
      end
  end.

find_path(Key,FD) ->
  find_path(FD,Key,read_blob_bw(FD,eof),[]).

find_path(FD,Key,{Node,_},O) ->
  case Node of
    <<"ABETS v1">> ->
      [];
    #internal{pointer=Pointer,recs=Recs} ->
      find_path(FD,Key,read_blob_fw(FD,new_pos(Key,Recs,Pointer)),[Node|O]);
    #leaf{} ->
      [Node|O]
  end.

new_pos(_Key,[],Pos)                          -> Pos;
new_pos(Key,[#rec{key=K}|_],Pos) when Key < K -> Pos;
new_pos(Key,Recs,_)                           -> new_pos(Key,Recs).

new_pos(_Key,[#rec{pointer=Pos}])                           -> Pos;
new_pos(Key,[#rec{pointer=Pos},#rec{key=K}|_]) when Key < K -> Pos;
new_pos(Key,[_|Recs])                                       -> new_pos(Key,Recs).

%%% commit bulk cache and exit bulk mode
do_bulk(commit,State = #state{fd=FD,bulk_nodes=[Leaf|Nodes]}) ->
  C = insert_node([],[Leaf],epos(FD),Nodes),
  cache_commit(FD,C),
  {ok,State#state{bulk_nodes=[]}}.

%%% insert a new rec in bulk mode
do_bulk(_,_,State = #state{name=Name,bulk_nodes=[]}) ->
  {{not_in_bulk_mode,Name},State};
do_bulk(Key,Val,State = #state{fd=FD,bulk_nodes=[Leaf|OldNodes]}) ->
  {Bin,Type,Len,Size} = pack_val(Val),
  Pos = epos(FD),
  Node = update_node([#rec{key=Key,pointer=Pos}],Leaf),
  OldCache = insert_node([{Len,Type,Bin}],Node,Pos+Size,OldNodes),
  {Cache,Nodes} = maybe_flush_cache(OldCache),
  cache_commit(FD,Cache),
  {ok,State#state{bulk_nodes=Nodes}}.

maybe_flush_cache(Cache) ->
  lists:foldl(fun flusher/2,{[],[]},Cache).

flusher({_,?TYPE_INTERNAL,_} = X,{C,N}) -> {C,N++[X]};
flusher({_,?TYPE_LEAF,_} = X,{C,N})     -> {C,N++[X]};
flusher({_,?TYPE_TERM,_} = X,{C,N})     -> {C++[X],N};
flusher({_,?TYPE_BINARY,_}   = X,{C,N}) -> {C++[X],N}.

%%% insert new rec by writing the value and rebuilding the nodes above
%%% and including the rec's leaf
do_insert(_,_,#state{bulk_nodes=[_|_]}) ->
  in_bulk_mode;
do_insert(Key,Val,#state{fd=FD,bulk_nodes=[]}) ->
  {Bin,Type,Len,Size} = pack_val(Val),
  [Leaf|Nodes] = find_path(Key,FD),
  Pos = epos(FD),
  Node = update_node([#rec{key=Key,pointer=Pos}],Leaf),
  Cache = insert_node([{Len,Type,Bin}],Node,Pos+Size,Nodes),
  cache_commit(FD,Cache).

% node is the root
insert_node(OldCache,[Node],Pos,[]) ->
  {_,_,Cache} = pack_node(OldCache,Pos,Node),
  Cache;
%% the root has split
insert_node(C0,[XNode,YNode],Pos,[]) ->
  {_XRec,XSize,C1} = pack_node(C0,Pos,XNode),
  {_YRec,YSize,C2} = pack_node(C1,Pos+XSize,YNode),
  {_,_,Cache} = pack_node(C2,Pos+XSize+YSize,split_root(YNode,Pos,XSize)),
  Cache;
%% XNode is a new child of OldNode
insert_node(C0,[XNode],Pos,[OldNode|Nodes]) ->
  {Rec,Size,C1} = pack_node(C0,Pos,XNode),
  insert_node(C1,update_node([Rec],OldNode),Pos+Size,Nodes);
%% OldNode has 2 new kids, XNode and YNode
insert_node(C0,[XNode,YNode],Pos,[OldNode|Nodes]) ->
  {XRec,XSize,C1} = pack_node(C0,Pos,XNode),
  {YRec,YSize,C2} = pack_node(C1,Pos+XSize,YNode),
  insert_node(C2,update_node([XRec,YRec],OldNode),Pos+XSize+YSize,Nodes).

split_root(YNode,XPos,YSize) ->
  #internal{size=2,pointer=XPos,
            recs=[#rec{key=YNode#internal.prog,
                       pointer=XPos+YSize}]}.

%% insert a rec in a leaf
update_node([Rec],Node = #leaf{recs=OldRecs}) ->
  Size = length(Recs = new_recs_leaf(Rec,OldRecs)),
  maybe_split(Node#leaf{size=Size,recs=Recs});
%% insert a rec in an empty internal node
update_node([#rec{pointer=Pointer}],Node = #internal{recs=[]}) ->
  [Node#internal{size=1,pointer=Pointer}];
%% insert an empty rec in an empty internal node
update_node([Pointer],Node = #internal{recs=[]}) when is_integer(Pointer) ->
  [Node#internal{size=0,pointer=Pointer}];
%% insert 2 recs in an empty internal node
update_node([R1,R2], Node = #internal{recs=[]}) ->
  [Node#internal{size=2,pointer=R1#rec.pointer,recs=[R2]}];
%% insert a rec in an existing internal node
update_node([R0],Node = #internal{recs=Recs}) ->
  case is_leftmost(R0,Recs) of
    true -> [Node#internal{pointer=R0#rec.pointer}];
    false-> [Node#internal{recs = new_recs_internal(R0,Recs)}]
  end;
%% insert 2 recs in an existing internal rec
update_node([R1,R2],Node = #internal{recs=Recs}) ->
  case is_leftmost(R1, Recs) of
    true ->
      Size = length(Rs = [R2|Recs])+1,
      maybe_split(Node#internal{size=Size,pointer=R1#rec.pointer,recs=Rs});
    false->
      Rs = grow_recs(Recs,R1,R2),
      maybe_split(Node#internal{size=length(Rs)+1,recs=Rs})
  end.

is_leftmost(R,[R0|_]) ->
  R#rec.key =:= undefined orelse R#rec.key < R0#rec.key.

% here we either replace a record (if the key exists), or grow the record list
new_recs_leaf(R,[])                                   -> [R];
new_recs_leaf(R=#rec{key=K},[#rec{key=K}|Recs])       -> [R|Recs];
new_recs_leaf(R0=#rec{key=K0},[R1=#rec{key=K1}|Recs]) ->
  case K0 < K1 of
    true -> [R0,R1|Recs];
    false-> [R1|new_recs_leaf(R0,Recs)]
  end.

%% here we make the record list longer
grow_recs([_],R1,R2) ->
  [R1,R2];
grow_recs([R0,Rn|Recs],R1,R2) ->
  case R1#rec.key < Rn#rec.key of
    true -> [R1,R2,Rn|Recs];
    false-> [R0|grow_recs([Rn|Recs],R1,R2)]
  end.

% here we replace a record. the record list does not grow
new_recs_internal(#rec{pointer=Pointer},[Rec]) ->
  [Rec#rec{pointer=Pointer}];
new_recs_internal(R0 = #rec{key=K0,pointer=Pointer},[R1,R2|Recs]) ->
  case K0 < R2#rec.key of
    true -> [R1#rec{pointer=Pointer},R2|Recs];
    false-> [R1|new_recs_internal(R0,[R2|Recs])]
  end.

maybe_split(Node) ->
  case node_size(Node) =< ?ORDER2 of
    true -> [Node];
    false-> split(Node)
  end.

split(Node = #internal{recs=Recs}) ->
  {A,[H|T]} = lists:split(length(Recs) div 2,Recs),
  [Node#internal{type=normal,size=length(A)+1,recs=A},
   Node#internal{type=normal,size=length(T)+1,
                 prog=H#rec.key,pointer=H#rec.pointer,recs=T}];

split(Node = #leaf{recs=Recs}) ->
  {A,B} = lists:split(length(Recs) div 2,Recs),
  [Node#leaf{size=length(A),recs=A},
   Node#leaf{size=length(B),recs=B}].

node_size(#internal{size=Size}) -> Size;
node_size(    #leaf{size=Size}) -> Size.

pack_node(Cache,Pos,Node) ->
  {Bin,Type,Len,Size} = pack_val(Node),
  {node_to_rec(Node,Pos),Size,[{Len,Type,Bin}|Cache]}.

node_to_rec(#internal{prog=Key},Pointer) -> #rec{key=Key,pointer=Pointer};
node_to_rec(#leaf{recs=[]},Pointer)      -> Pointer;
node_to_rec(#leaf{recs=Recs},Pointer)    -> node_to_rec(hd(Recs),Pointer);
node_to_rec(#rec{key=Key},Pointer)       -> #rec{key=Key,pointer=Pointer}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% file ops

do_bulk(Tab) ->
  file:delete(filename(Tab)),
  {FD,[]} = do_open(Tab),
  write(FD,[{?TYPE_BINARY,?HEADER}]),
  {FD,[#leaf{},#internal{}]}.

do_create(Tab) ->
  file:delete(filename(Tab)),
  {FD,[]} = do_open(Tab),
  Pointer = byte_size(?HEADER)+?PAD_BYTES+?PAD_BYTES,
  {LeafBin,LeafType,_,_} = pack_val(#leaf{}),
  {RootBin,RootType,_,_} = pack_val(#internal{pointer=Pointer}),
  write(FD,[{?TYPE_BINARY,?HEADER},{LeafType,LeafBin},{RootType,RootBin}]),
  {FD,[]}.

do_open(Tab) ->
  {ok,FD} = file:open(filename(Tab),[read,append,binary,raw]),
  {FD,[]}.

write(FD,IOlist) ->
  ok = file:write(FD,[wrap(E) || E <- IOlist]),
%  file:sync(FD),
  ok.

%% pos @ eof
epos(FD) ->
  {ok,Pos} = file:position(FD,eof),
  Pos.

cache_commit(FD,Cache) ->
  write(FD,reverse_cache(Cache,[])).

reverse_cache([{_,Type,Bin}|Cache],O) -> reverse_cache(Cache,[{Type,Bin}|O]);
reverse_cache([],O) -> O.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% disk format

wrap({Type,Binary}) when is_binary(Binary) ->
  BS = byte_size(Binary),
  Sz = <<BS:?SIZE_BITS/integer>>,
  [Sz,Type,Binary,Type,Sz].

read_blob_bw(FD,eof) -> read_blob_bw(FD,epos(FD));
read_blob_bw(FD,End) ->
  {Ptr,Size,Bin} = read(FD,erlang:max(0,End-?BLOCK_SIZE),End),
  [exit({bin_error1,{Size}}) || Size < ?TYPE_BYTES+?SIZE_BYTES],
  Off = Size-?TYPE_BYTES-?SIZE_BYTES,
  <<_:Off/binary,Type:?TYPE_BYTES/binary,BS:?SIZE_BITS/integer>> = Bin,
  [exit({bin_error2,{Size,BS}}) || Size < BS+(?PAD_BYTES+?PAD_BYTES)],
  Of = Size-BS-(?PAD_BYTES+?PAD_BYTES),
  <<_:Of/binary,_:?PAD_BYTES/binary,BT:BS/binary,_:?PAD_BYTES/binary>> = Bin,
  [exit({bin_error3,{Size,BS}}) || Ptr+Of =/= End-(BS+?PAD_BYTES+?PAD_BYTES)],
  {unpack(Type,BT),Ptr+Of}.

% case get(read_cache) of
%   {CPtr,CSize,CBin} when CPtr+?SIZE_BYTES < End, End =< CPtr+CSize ->
%     Len = End-CPtr-?SIZE_BYTES,
%     Off = CSize-Len-?SIZE_BYTES,
%     <<B:Len/binary,Size:?SIZE_BITS/integer,_:Off/binary>> = CBin,
%     case Size+?TYPE_BYTES =< Len of
%       true ->
%         O = Len-Size-?TYPE_BYTES,
%         <<_:O/binary,BT:Size/binary,Type:?TYPE_BYTES/binary>> = B,
%         {unpack(Type,BT),CPtr+O-?TYPE_BYTES-?SIZE_BYTES};
%       false->
%         case ?BLOCK_SIZE < End of
%           true -> read(FD,End-?BLOCK_SIZE,End);
%           false-> read(FD,End-Size-?PADDING,End)
%         end,
%         read_blob_bw(FD,End)
%     end;
%   _ ->
%     case End < ?BLOCK_SIZE of
%       true -> Beg = 0;
%       false-> Beg = End-?BLOCK_SIZE
%     end,
%     read(FD,Beg,End),
%     read_blob_bw(FD,End)
% end.

read_blob_fw(FD,Beg) ->
  {Beg,Size,Bin} = read(FD,Beg,Beg+?BLOCK_SIZE),
  [exit({blob_error,{Size}}) || Size < ?PAD_BYTES],
  <<Sz:?SIZE_BITS/integer,Type:?TYPE_BYTES/binary,_/binary>> = Bin,
  [exit({blob_error,{Size,Sz}}) || Size < Sz+?PAD_BYTES],
  <<_:?PAD_BYTES/binary,BT:Sz/binary,_/binary>> = Bin,
  {unpack(Type,BT),Beg}.

% read_blob_fw(FD,Beg) ->
%   case get(read_cache) of
%     {CPtr,CSize,CBin} when CPtr =< Beg, Beg < CPtr+CSize-?SIZE_BYTES ->
%       Off = Beg-CPtr,
%       <<_:Off/binary,Size:?SIZE_BITS/integer,B/binary>> = CBin,
%       Len = byte_size(B),
%       case Size+?TYPE_BYTES < Len of
%         true ->
%           <<Type:?TYPE_BYTES/binary,BT:Size/binary,_/binary>> = B,
%           {unpack(Type,BT),Beg};
%         false->
%           End = Beg+Size+?PAD_BYTES+?PAD_BYTES,
%           case ?BLOCK_SIZE < End of
%             true -> Start = 0, Stop = ?BLOCK_SIZE;
%             false-> Start = End-?BLOCK_SIZE, Stop = End
%           end,
%           read(FD,Start,Stop),
%           read_blob_fw(FD,Beg)
%       end;
%     _ ->
%       case (Epos = epos(FD)) < Beg+?BLOCK_SIZE of
%         true -> Start = lists:max([0,Epos-?BLOCK_SIZE]),Stop = Epos;
%         false-> Start = Beg,                            Stop = Beg+?BLOCK_SIZE
%       end,
%       read(FD,Start,Stop),
%       read_blob_fw(FD,Beg)
%   end.

read(FD,Beg,End) ->
  [exit({read_error,{Beg}}) || Beg < 0],
  [exit({read_error,{Beg,End}}) || End < Beg],
  {ok,Bin} = file:pread(FD,Beg,End-Beg),
  Size = byte_size(Bin),
  {Beg,Size,Bin}.
%  put(read_cache,{Beg,Size,Bin}).

unpack(Type,B) ->
  case Type of
    ?TYPE_BINARY -> B;
    _            -> binary_to_term(B)
  end.

pack_val(Val) ->
  Bin = to_binary(Val),
  {Bin,
   type(Val),
   rec_len(Val),
   byte_size(Bin)+?PAD_BYTES+?PAD_BYTES}.

type(#internal{})         -> ?TYPE_INTERNAL;
type(#leaf{})             -> ?TYPE_LEAF;
type(B) when is_binary(B) -> ?TYPE_BINARY;
type(_)                   -> ?TYPE_TERM.

rec_len(#internal{size=Len}) -> Len;
rec_len(#leaf{size=Len})     -> Len;
rec_len(_)                   -> null.
  
to_binary(Term) ->
  term_to_binary(Term,[{compressed,3},{minor_version,1}]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% ad-hoc unit testing

unit_bulk() ->
  catch abets:destroy(foo),
  abets:new(foo,[bulk]),
  [abets:bulk(foo,N,{mange,1})||N<-[10,11]].

unit() ->
  unit(10000).

unit(N) when is_integer(N) -> unit(shuffle(lists:seq(1,N)));
unit(L) when is_list(L) ->
  catch abets:destroy(foo),
  io:fwrite("length: ~p~n",[length(L)]),
  abets:new(foo),
  [abets:insert(foo,E,{tobbe,E}) || E <- L],
  try length([{tobbe,E}=abets:lookup(foo,E) || E <- L])
  catch _:R -> R
  end.

shuffle(L) ->
  [V||{_,V}<-lists:sort([{random:uniform(),E}||E<-L])].

% qc() ->
%   ?FORALL(L,
%           ?SIZED(S,resize(S*S*S*S,list(int()))),
%           abets:unit(L)==length(L)).

wunit() -> wunit(10000).

wunit(N) when is_integer(N) -> wunit(shuffle(lists:seq(1,N)));
wunit(L) when is_list(L) ->
  catch abets:destroy(foo),
  abets:new(foo),
  try [wunit(E,L) || E <- L],length(L)
  catch _:R -> R
  after abets:close(foo)
  end.

wunit(E,L) ->
  abets:insert(foo,E,{tobbe,E}),
  Ss = sub(L,E),
  try length([{tobbe,I}=abets:lookup(foo,I) || I <- Ss])
  catch _:R -> exit({R,E,Ss})
  end.

sub([E|_],E) -> [E];
sub([H|T],E) -> [H|sub(T,E)].


%% counters;
%% [1,2,3,4,5,7,8,9,10,11,12,6]
%% [5,20,15,10,4,11,6,16,19,8,13,14,2,17,18,12,3,1,7,9]
