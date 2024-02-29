From elpi.apps.NES Extra Dependency "nes_synterp.elpi" as nes_synterp.
From elpi.apps.NES Extra Dependency "nes_interp.elpi" as nes_interp.

From elpi Require Import elpi.

Set Warnings "+elpi".

#[phase="both"] Elpi Db NES.db lp:{{

pred open-ns o:string, o:list string.
:name "open-ns:begin"
open-ns _ _ :- fail.

typeabbrev path (list string).

:index (2)
pred ns o:path, o:modpath.

}}.


Elpi Command NES.Status.
#[phase="both"] Elpi Accumulate Db NES.db.
#[synterp] Elpi Accumulate File nes_synterp.
#[synterp] Elpi Accumulate lp:{{

main _ :-
  coq.say "NES: current namespace" {nes.current-path},
  std.findall (ns Y_ Z_) NS,
  coq.say "NES: registered namespaces" NS.

}}.
#[interp] Elpi Accumulate lp:{{ main _. }}.
Elpi Typecheck.
Elpi Export NES.Status.

Elpi Command NES.OldBegin.
#[synterp] Elpi Accumulate File nes_synterp.
#[synterp] Elpi Accumulate lp:{{

  main [str NS] :- !, nes.begin-path {nes.string->non-empty-ns NS} _.
  main _ :- coq.error "usage: NES.Begin <DotSeparatedPath>".

}}.
#[synterp] Elpi Accumulate Db NES.db.
#[interp] Elpi Accumulate lp:{{ main _ :- coq.replay-all-missing-synterp-actions. }}.
Elpi Typecheck.
Elpi Export NES.OldBegin.

Elpi Command NES.OldEnd.
#[synterp] Elpi Accumulate File nes_synterp.
#[synterp] Elpi Accumulate lp:{{

  main [str NS] :- nes.end-path {nes.string->non-empty-ns NS} _.
  main _ :- coq.error "usage: NES.End <DotSeparatedPath>".

}}.
#[synterp] Elpi Accumulate Db NES.db.
#[interp] Elpi Accumulate lp:{{ main _ :- coq.replay-all-missing-synterp-actions. }}.
Elpi Typecheck.
Elpi Export NES.OldEnd.

Elpi Command NES.Begin.
#[synterp] Elpi Accumulate File nes_synterp.
#[interp] Elpi Accumulate File nes_interp.
#[phase="both"] Elpi Accumulate Db NES.db.
#[phase="both"] Elpi Accumulate lp:{{

  main [str NS] :- !, nes.begin-path {nes.string->non-empty-ns NS} _.
  main _ :- coq.error "usage: NES.Begin <DotSeparatedPath>".

}}.
Elpi Typecheck.
Elpi Export NES.Begin.

Elpi Command NES.End.
#[synterp] Elpi Accumulate File nes_synterp.
#[interp] Elpi Accumulate File nes_interp.
#[phase="both"] Elpi Accumulate Db NES.db.
#[phase="both"] Elpi Accumulate lp:{{

  main [str NS] :- nes.end-path {nes.string->non-empty-ns NS} _.
  main _ :- coq.error "usage: NES.End <DotSeparatedPath>".

}}.
Elpi Typecheck.
Elpi Export NES.End.


Elpi Command NES.Open.
#[synterp] Elpi Accumulate File nes_synterp.
#[interp] Elpi Accumulate File nes_interp.
#[phase="both"] Elpi Accumulate Db NES.db.
#[synterp] Elpi Accumulate lp:{{

  main [str NS] :- nes.open-path {nes.resolve NS}.
  main _ :- coq.error "usage: NES.Open <DotSeparatedPath>".

}}.
Elpi Typecheck.
Elpi Export NES.Open.

(* List the contents a namespace *)
Elpi Command NES.ListJanno.
#[phase="both"] Elpi Accumulate Db NES.db.
#[synterp] Elpi Accumulate File nes_synterp.
#[interp] Elpi Accumulate File nes_interp.
#[synterp] Elpi Accumulate lp:{{ main _. }}.
#[interp] Elpi Accumulate lp:{{

  pred pp-gref i:gref, o:coq.pp.
  pp-gref GR PP :- coq.term->pp (global GR) PP.

  main [str NS] :-
    nes.resolve NS Path, std.findall (ns O_ P_) DB,
    DB => nes.print-path Path pp-gref.
  main _ :- coq.error "usage: NES.ListJanno <DotSeparatedPath>".

}}.
Elpi Typecheck.
Elpi Export NES.ListJanno.


(* List the contents a namespace *)
Elpi Command NES.List.
#[phase="both"] Elpi Accumulate Db NES.db.
#[synterp] Elpi Accumulate File nes_synterp.
#[interp] Elpi Accumulate File nes_interp.
#[synterp] Elpi Accumulate lp:{{
  main-synterp [str NS] (pr DB Path) :- nes.resolve NS Path, std.findall (ns O_ P_) DB.
}}.
#[interp] Elpi Accumulate lp:{{

  pred pp-gref i:gref, o:coq.pp.
  pp-gref GR PP :- coq.term->pp (global GR) PP.

  main-interp [str _] (pr DB Path) :- DB => nes.print-path Path pp-gref.
  main-interp _ _ :- coq.error "usage: NES.List <DotSeparatedPath>".

}}.
Elpi Typecheck.
Elpi Export NES.List.

(* NES.List with types *)
Elpi Command NES.Print.
#[phase="both"] Elpi Accumulate Db NES.db.
#[synterp] Elpi Accumulate File nes_synterp.
#[interp] Elpi Accumulate File nes_interp.
#[synterp] Elpi Accumulate lp:{{
  main-synterp [str NS] (pr DB Path) :- nes.resolve NS Path, std.findall (ns O_ P_) DB.
}}.
Elpi Accumulate lp:{{

  pred pp-gref i:gref, o:coq.pp.
  pp-gref GR PP :- std.do! [
    coq.env.typeof GR Ty,
    PP = coq.pp.box (coq.pp.hov 2) [
      {coq.term->pp (global GR)}, coq.pp.str " :", coq.pp.spc,
      {coq.term->pp Ty},
    ],
  ].

  main-interp [str _] (pr DB Path) :- DB => nes.print-path Path pp-gref.
  main _ :- coq.error "usage: NES.Print <DotSeparatedPath>".

}}.
Elpi Typecheck.
Elpi Export NES.Print.
