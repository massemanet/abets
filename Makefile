all: compile

compile:
	./rebar3 compile

test: eunit

eunit:
	./rebar3 eunit --cover
	./rebar3 cover
