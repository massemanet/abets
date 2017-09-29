%% -*- mode: erlang; erlang-indent-level: 2 -*-
%% @doc
%% @end

-module(abets_eunit).

-include_lib("eunit/include/eunit.hrl").

basic_test_() ->
    {inorder,
     {"basic happy testing.",
      {foreach,
       fun start/0,
       fun stop/1,
       [fun t_bulk/1,
        fun t_unit/1,
        fun t_next/1]
      }}}.

start() ->
  catch abets:destroy(foo).

stop(_) ->
  ok.

t_next(_) ->
  [fun() -> nxt() end].

nxt() ->
  abets:new(foo),
  [abets:insert(foo, {k, I}, {v, I}) || I <- lists:seq(1,5,2)],
  ?assertMatch({{k, 1}, {v, 1}}, abets:next(foo, {k, 0})),
  ?assertMatch({{k, 3}, {v, 3}}, abets:next(foo, {k, 2})),
  ?assertMatch({not_found, {k, 6}, _}, abets:next(foo, {k, 6})).

t_bulk(_) ->
  [fun() -> bulk(33) end].

bulk(M) ->
  [(fun ubf/1)(N) || N <- lists:seq(1, M)].

ubf(M)->
  catch abets:destroy(foo),
  Seq = lists:seq(1, M),
  abets:new(foo, [bulk]),
  [abets:bulk(foo, {k, N}, {v, N}) || N <- Seq],
  abets:bulk(foo, commit),
  [try {v, N} = abets:lookup(foo, {k, N})
   catch _:R -> exit({R, N, lists:last(Seq)})
   end || N <- Seq].

t_unit(_) ->
  [fun() -> unit(100) end].

unit(N) when is_integer(N) -> unit(shuffle(lists:seq(1, N)));
unit(L) when is_list(L) ->
  abets:new(foo),
  try [unit(E, L) || E <- L], length(L)
  catch _:R -> R
  end.

unit(E, L) ->
  abets:insert(foo, E, {tobbe, E}),
  Ss = sub(L, E),
  try length([{tobbe, I} = abets:lookup(foo, I) || I <- Ss])
  catch _:R -> exit({R, E, Ss})
  end.

sub([E|_], E) -> [E];
sub([H|T], E) -> [H|sub(T, E)].

shuffle(L) ->
  [V || {_, V} <- lists:sort([{rand:uniform(), E} || E <- L])].
