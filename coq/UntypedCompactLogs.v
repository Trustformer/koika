(*! Language | Untyped compact logs of reads and writes !*)
Require Export Koika.Common Koika.Environments Koika.Syntax.

Section Logs.
  Context {V: Type}.

  Set Primitive Projections.
  Record LogEntry := LE {
    lread0: bool; lread1: bool; lwrite0: option V; lwrite1: option V
  }.
  Unset Primitive Projections.

  Arguments LogEntry : clear implicits.

  Context {reg_t: Type}.
  Context {REnv: Env reg_t}.
  Definition R : reg_t -> Type := fun _ => V.

  Definition _UCLog := REnv.(env_t) (fun idx => LogEntry).
  Notation UCLog := _UCLog.

  Definition logentry_empty : LogEntry := {|
    lread0 := false; lread1 := false; lwrite0 := None; lwrite1 := None
  |}.

  Definition log_empty : UCLog := REnv.(create) (fun _ => logentry_empty).

  Definition opt_or {A} (o1 o2: option A) :=
    match o1 with
    | Some _ => o1
    | None   => o2
    end.

  Definition logentry_app (l1 l2: LogEntry) := {|
    lread0  := l1.(lread0) || l2.(lread0);
    lread1  := l1.(lread1) || l2.(lread1);
    lwrite0 := opt_or l1.(lwrite0) l2.(lwrite0);
    lwrite1 := opt_or l1.(lwrite1) l2.(lwrite1)
  |}.

  Definition log_app (l1 l2: UCLog) :=
    map2 REnv (fun _ => logentry_app) l1 l2.

  Open Scope bool_scope.

  Definition may_read0 (sched_log: UCLog) idx :=
    match REnv.(getenv) sched_log idx with
    | {| lread0 := _; lread1 := _; lwrite0 := None; lwrite1 := None |} => true
    | _ => false
    end.

  Definition may_read1 (sched_log: UCLog) idx :=
    match REnv.(getenv) sched_log idx with
    | {| lread0 := _; lread1 := _; lwrite0 := _; lwrite1 := None |} => true
    | _ => false
    end.

  Definition may_write0 (sched_log rule_log: UCLog) idx :=
    match REnv.(getenv) sched_log idx, REnv.(getenv) rule_log idx with
    | {| lread0 := _; lread1 := false; lwrite0 := None; lwrite1 := None |},
      {| lread0 := _; lread1 := false; lwrite0 := None; lwrite1 := None |}
      => true
    | _, _ => false
    end.

  Definition may_write1 (sched_log rule_log: UCLog) idx :=
    match REnv.(getenv) sched_log idx, REnv.(getenv) rule_log idx with
    | {| lread0 := _; lread1 := _; lwrite0 := _; lwrite1 := None |},
      {| lread0 := _; lread1 := _; lwrite0 := _; lwrite1 := None |}
      => true
    | _, _ => false
    end.

  Definition commit_update (r0: REnv.(env_t) R) (log: UCLog) : REnv.(env_t) R :=
    REnv.(create) (
      fun k => let rl := REnv.(getenv) log k in
        match rl.(lwrite1), rl.(lwrite0) with
        | Some v, _       => v
        | _     , Some v  => v
        | None  , None    => REnv.(getenv) r0 k
        end
    ).

End Logs.

Arguments LE {V} lread0 lread1 lwrite0 lwrite1 : assert.
Arguments LogEntry: clear implicits.
Arguments logentry_app {V} !l1 !l2 /: assert.
