=========================================================
 |koika|: A Core Language for Rule-Based Hardware Design
=========================================================

This is the home of |koika|, an experimental hardware design language inspired by `BlueSpec SystemVerilog <http://wiki.bluespec.com/>`_.  |koika| programs are built from *rules*, small bits of hardware that operate concurrently to compute state updates but provide `the illusion of serializable (atomic) updates <atomic-actions_>`_.  |koika| has simple, precise semantics that give you `strong guarantees about the behavior of your designs <oraat_>`_.

Our distribution includes an `executable reference implementation of the language <formal-semantics_>`_ written using the `Coq proof assistant <https://coq.inria.fr/>`_, machine-checked proofs ensuring that |koika|'s semantics are compatible with `one-rule-at-a-time execution <oraat_>`_, and a `formally-verified compiler <compiler-verification_>`_ that generates circuits guaranteed to correctly implement your designs.

|koika| programs are typically written inside of Coq using an `embedded DSL <syntax_>`_ (this lets you leverage Coq's powerful metaprogramming features and modular abstractions), though we also have a more limited `standalone front-end <lispy-verilog_>`_ that accepts programs in serialized (s-expressions) form.  For simulation, debugging, and testing purposes, |koika| programs can be compiled into `readable, cycle-accurate C++ models <cuttlesim_>`_, and for synthesis the |koika| compiler targets a minimal subset of synthesizable Verilog supported by all major downstream tools.

|koika| is a research prototype: the circuits that our compiler generates typically have reasonable-to-good performance and area usage, but our RTL optimizer is very simple and can miss obvious improvements.  Because our simulator can take advantage of high-level information, |koika| designs typically run reasonably fast in C++ simulation.

Our largest example at the moment is a simple RISCV (RV32I) `4-stage pipelined core <examples/rv/RVCore.v>`_.

|koika| is currently developed as a joint research effort at MIT, involving members of CSG (the Computation Structure Group) and PLV (the Programming Languages & Verification group).  Our `latest draft <koika-paper_>`_ is a good place to get details about the research that powers it.  The name “|koika|” (甲イカ) is Japanese for “`cuttlefish <https://en.wikipedia.org/wiki/Cuttlefish>`_”; we chose it because cuttlefishes have blue blood (a tribute to the name Bluespec), and because their eight arms are equipped with independent neurons that allow them operate semi-independently towards a shared purpose, much like rules in |koika| designs.

This README provides practical information to get started with Kôika.  For details about Kôika's semantics, its compilation algorithm, and the work it draws inspiration from, please read our PLDI 2020 paper: `The Essence of Bluespec, A Core Language for Rule-Based Hardware Design <https://dl.acm.org/doi/10.1145/3385412.3385965>`_.

.. raw:: html

   <a href="https://github.com/mit-plv/koika/">
     <img src="https://raw.githubusercontent.com/mit-plv/koika/master/etc/logo/cover.jpg" align="center" />
   </a>

Getting started
===============

Installing dependencies and building from source
------------------------------------------------

* OCaml 4.07 through 4.09, `opam <https://opam.ocaml.org/doc/Install.html>`_ 2.0 or later, GNU make.

* Coq 8.11 through 8.13::

    opam install coq=8.12.2

* Dune 2.5 or later::

    opam upgrade dune

* Some OCaml packages::

    opam install base core stdio parsexp hashcons zarith

* To run the tests of our RISCV core, a `RISCV compilation toolchain <https://github.com/xpack-dev-tools/riscv-none-embed-gcc-xpack/releases/>`_.

* To run C++ simulations: a recent C++ compiler (clang or gcc) and
  ``libboost-dev``.

You can compile the full distribution, including examples, tests, and proofs by running ``make`` in the top-level directory of this repo.  Generated files are placed in ``_build``, ``examples/_objects/``,  ``tests/_objects/``, and  ``examples/rv/_objects/``.

Each directory in ``_objects`` contains `a Makefile <makefile_>`_ to ease further experimentation (including RTL simulation, profiling, trace generation, etc.).

.. opam show -f name,version coq dune base core stdio parsexp hashcons zarith | sed 's/name *//' | tr '\n' ' ' | sed 's/ *version */=/g' | xclip

For reproducibility, here is one set of versions known to work:

- OCaml 4.09 with ``opam install base=v0.13.1 coq=8.11.1 core=v0.13.0 dune=2.5.1 hashcons=1.3 parsexp=v0.13.0 stdio=v0.13.0 zarith=1.9.1``

Browsing examples
-----------------

The ``examples/`` directory of this repo demonstrates many of |koika|'s features.
The examples can be compiled using ``make examples``, and browsed in either
CoqIDE or Proof General.  There is basic Emacs support for ``.lv`` files (the “Lispy
Verilog” alternative frontend for |koika|) in ``etc/lv-mode.el``.

See `browsing the sources <repo-map_>`_ below for information about the repository's organization.

Compiling your own programs
---------------------------

Our compiler (``cuttlec``) supports multiple targets:

- ``verilog`` (an RTL implementation of your design expressed in the synthesizable subset of Verilog 2000)
- ``hpp`` (a cuttlesim model of your design, i.e. a cycle-accurate C++ implementation of it, useful for debugging)
- ``cpp`` (a driver for the cuttlesim model of your design)
- ``verilator`` (a simple C++ driver to simulate the Verilog using Verilator)
- ``makefile`` (an auto-generated Makefile including convenient targets to debug, profile, trace, or visualize the outputs of your design)
- ``dot`` (a basic representation of the RTL generated from your design)

For quick experimentation, you can just drop your files in ``examples/`` or ``tests/`` and run ``make examples/_objects/<your-file.v>/``.

Programs written in the Coq EDSL
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

On the Coq side, after implementing your design, use the following to define a “package” (see the `<examples/>`_ directory for more information, or read the `<syntax_>`_ section below):

.. code:: coq

   Definition package :=
     Interop.Backends.register
       {| ip_koika := …;
          ip_sim := …;
          ip_verilog := … |}.
   Extraction "xyz.ml" package.

Compile your Coq sources using ``coqc`` or ``dune`` to generate ``xyz.ml``, then compile that file using ``cuttlec xyz.ml -T …``.

Among other things, a package contains instances of the ``Show`` typeclass used to print register names.  These instances are typically derived automatically, but customizing them makes it possible to control the names given to signals in the generated Verilog and C++ code (for example, instead of ``x0``, ``x1``, …, ``x31``, we use ``zero``, ``ra``, ``sp``, ``gp``, etc. in the RISCV core).

Programs written in serialized syntax (“Lispy Verilog”)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Use ``cuttlec your-program.lv -T verilog``, or any other output option as described by ``cuttlec --help``.

Technical overview
==================

.. _koika-paper:

Details about |koika|\ 's design and implementation can be found in our `research paper <https://pit-claudel.fr/clement/papers/koika-PLDI20.pdf>`_.

Execution model
---------------

.. _atomic-actions:

|koika| programs are made of *rules*, orchestrated by a *scheduler*.  Each rule is a program that runs once per cycle, as long as it does not conflict with other rules.  When conflicts arise (for example, when two rules attempt to write to the same register), the priority order specified by the scheduler determines which rule gets to fire (i.e. execute).  Concretely, a rule might look like this (this is a rule that takes one step towards computing the GCD of the numbers in registers ``gcd_a`` and ``gcd_b``):

.. code:: coq

   Definition gcd_compute := {{
     let a := read0(gcd_a) in
     let b := read0(gcd_b) in
     if a != |16`d0| then
       if a < b then
         write0(gcd_b, a);
         write0(gcd_a, b)
       else
         write0(gcd_a, a - b)
     else
       fail
   }}

.. _oraat:

The semantics of |koika| guarantee that each rule executes atomically, and that generated circuits behave one-rule-at-a-time — that is, even when multiple rules fire in the same cycle, the updates that they compute are as if only one rule had run per cycle (previous work used this property to define the language; in contrast, our semantics are more precise, and this atomicity property is proven in `<coq/OneRuleAtATime.v>`_).

As an example, consider a simple two-stage pipeline with two single-element input FIFOs and one single-element output FIFO:

.. image:: etc/readme/pipeline.svg

We implement these FIFOs using three single-bit registers (``…_empty``) indicating whether each FIFO is empty, and three data registers (``…_data``) holding the contents of these FIFOs.  We have three rules: two to dequeue from the input FIFOs into a middle FIFO (``deq0`` and ``deq1``), and one to dequeue from the middle FIFO and write a result (the input plus 412) into an output FIFO (``process``).  The code looks like this (``guard(condition)`` is short for ``if !condition then fail``):

.. code:: coq

   (* This is a compact way to define deq0, deq1, and process: *)
   Definition rules (rl: rule_name_t) :=
     match rl with
     | deq0 =>
       {{ guard(!read0(in0_empty) && read0(fifo_empty));
          write0(fifo_data, read0(in0_data));
          write0(fifo_empty, Ob~0);
          write0(in0_empty, Ob~1) }}
     | deq1 =>
       {{ guard(!read0(in1_empty) && read0(fifo_empty));
          write0(fifo_data, read0(in1_data));
          write0(fifo_empty, Ob~0);
          write0(in1_empty, Ob~1) }}
     | process =>
       {{ guard(!read1(fifo_empty) && read0(out_empty));
          write0(out_data, read1(fifo_data) + |32`d412|);
          write1(fifo_empty, Ob~1);
          write0(out_empty, Ob~0) }}
     end.

A conflict arises when both inputs are available; what should happen in this case? The ambiguity is resolved by the scheduler:

.. code:: coq

   Definition pipeline : scheduler :=
     deq0 |> deq1 |> process |> done.

This sequence indicates that ``deq0`` has priority, so ``in_data0`` is processed first.  When both inputs are available and the middle FIFO is empty, when ``deq1`` attempts to run, it will dynamically fail when trying to write into ``fifo_data``.

This example includes a simple form of backpressure: if the middle FIFO is full, the first two rules will not run; if the output FIFO is full, the last rule will not run.  This is made explicit by the ``guard`` statements (those would be hidden inside the implementation of the ``dequeue`` and ``enqueue`` methods of the FIFO in a larger example, as demonstrated `below <modularity_>`_).

Looking carefully, you'll notice that ``read``\ s and ``write``\ s are annotated with ``0``\ s and ``1``\ s.  These are forwarding specifications, or “ports”.  Values written at port 0 are visible in the same cycle at port 1, and values written at port 1 overwrite values written at port 0.  Hence, this example defines a bypassing FIFO: values written by ``deq0`` and ``deq1`` are processed by ``process`` in the same cycle as they are written, assuming that there is space in the output FIFO.  If we had used a ``read0`` instead, we would have had a pipelined FIFO.

In this example, starting with the following values::

   in0_empty  ⇒ false
   in0_data   ⇒ 42
   in1_empty  ⇒ false
   in1_data   ⇒ 73
   fifo_empty ⇒ true
   fifo_data  ⇒ 0
   out_empty  ⇒ true
   out_data   ⇒ 0

we get the following output::

   in0_empty  ⇒ true
   in0_data   ⇒ 42
   in1_empty  ⇒ false
   in1_data   ⇒ 73
   fifo_empty ⇒ true
   fifo_data  ⇒ 42
   out_empty  ⇒ false
   out_data   ⇒ 454

.. _koika-syntax:

Syntax
------

|koika| programs are written using an embedded DSL inside of the Coq proof assistant.  After compiling the distribution, begin your file with ``Require Import Koika.Frontend``.

Preamble and types
~~~~~~~~~~~~~~~~~~

Start by defining the following types:

- ``reg_t``: An enumerated type describing the state of your machine.  For example,

  .. code:: coq

     Inductive reg_t :=
     (* These bypassing FIFOs are used to communicate with the memory *)
     | to_memory (state: MemReqFIFO.reg_t)
     | from_memory (state: MemRespFIFO.reg_t)
     (* These FIFOs are used to connect pipeline stages *)
     | d2e (state: fromDecodeFIFO.reg_t)
     | e2w (state: fromExecuteFIFO.reg_t)
     (* The register file and the scoreboard track and record reads and writes *)
     | register_file (state: Rf.reg_t)
     | scoreboard (state: Scoreboard.reg_t)
     (* These are plain registers, not module instances *)
     | pc
     | epoch.

- ``ext_fn_t``: An enumerated type describing custom combinational primitives (custom IP) that your program should have access to (custom sequential IP is implemented using external rules, which are currently a work in progress; see `<examples/rv/RVCore.v>`_ for a concrete example).  Use ``empty_ext_fn_t`` if you don't use external IP in your design.  For example,

  .. code:: coq

     Inductive ext_fn_t :=
     | custom_adder (size: nat).

Then, declare the types of the data held in each part of your state and the signatures of your external (combinational) IP (we usually name these functions ``R`` and ``Sigma``).  (In addition to bitsets, registers can contain structures, enums, or arrays of values; examples of these are given below.)

.. code:: coq

   Definition R (reg: reg_t) :=
     match reg with
     (* The type of the other modules is opaque; it's defined by the Rf module *)
     | to_memory st => MemReqFIFO.R st
     | register_file st => Rf.R st
     …
     (* Our own state is described explicitly: *)
     | pc => bits_t 32
     | epoch => bits_t 1
     end.

.. code:: coq

   Definition Sigma (fn: ext_fn_t): ExternalSignature :=
     match fn with
     | custom_adder sz => {$ bits_t sz ~> bits_t sz ~> bits_t sz $}
     end.

As needed, you can define your own custom types; here are a few examples:

.. code:: coq

   Definition proto :=
     {| enum_name := "protocol";
        enum_members :=
          vect_of_list ["ICMP"; "IGMP"; "TCP"; "UDP"];
        enum_bitpatterns :=
          vect_of_list [Ob~0~0~0~0~0~0~0~1; Ob~0~0~0~0~0~0~1~0;
                        Ob~0~0~0~0~0~1~1~0; Ob~0~0~0~1~0~0~0~1] |}.

.. code:: coq

   Definition flag :=
     {| enum_name := "flag";
        enum_members := vect_of_list ["set"; "unset"];
        enum_bitpatterns := vect_of_list [Ob~1; Ob~0] |}.

.. code:: coq

   Definition ipv4_address :=
     {| array_len := 4;
        array_type := bits_t 8 |}.

.. code:: coq

   Definition ipv4_header :=
     {| struct_name := "ipv4_header";
        struct_fields :=
          [("version", bits_t 4);
           ("ihl", bits_t 4);
           ("dscp", bits_t 6);
           ("ecn", bits_t 2);
           ("len", bits_t 16);
           ("id", bits_t 16);
           ("reserved", enum_t flag);
           ("df", enum_t flag);
           ("mf", enum_t flag);
           ("fragment_offset", bits_t 13);
           ("ttl", bits_t 8);
           ("protocol", enum_t proto);
           ("checksum", bits_t 16);
           ("src", array_t ipv4_address);
           ("dst", array_t ipv4_address)] |}.

.. code:: coq

   Definition result (a: type) :=
     {| struct_name := "result";
        struct_fields := [("valid", bits_t 1); ("value", a)] |}.

.. code:: coq

   Definition response := result (struct_t ipv4_header).

Rules
~~~~~

The main part of your program is rules.  You have access to the following syntax (there is no distinction between expressions and statements; statements are just expressions returning unit):

``pass``
  Do nothing
``fail``
  Abort the current rule, reverting all state changes
``let var := val in body``
  Let bindings
``set var := val``
  Assignments
``stmt1; stmt2``
  Sequence
``if val then val1 else val2``
  Conditional
``match val with  | pattern => body…  return default: body``
  Switches (case analysis)
``read0(reg)``, ``read1(reg)``, ``write0(reg)``, ``write1(reg)``
  Read or write a register at port 0 or 1
``pack(val)``, ``unpack(type, val)``
  Pack a value (go from struct, enum, or arrays to bits) or unpack a bitset
``get(struct, field)``, ``subst(struct, field, value)``
  Get a field of a struct value, or replace a field in a struct value (without mutating the original one)
``getbits(struct, field)``, ``substbits(struct, field, value)``
  Like get and subst, but on packed bitsets
``!x``, ``x && y``, ``x || y``, ``x ^ y``
  Logical operators (not, and, or, xor)
``x + y``, ``x - y``, ``x << y``, ``x >> y``, ``x >>> y``, ``zeroExtend(x, width)``, ``sext(x, width)``
  Arithmetic operators (plus, minus, logical shits, arithmetic shift right, left zero-extension, sign extension)
``x < y``, ``x <s y``, ``x > y``, ``x >s y``, ``x <= y``, ``x <s= y``, ``x >= y``, ``x >s= y``, ``x == y``, ``x != y``
  Comparison operators, signed and unsigned
``x ++ y``, ``x[y]``, ``x[y :+ z]``
  Bitset operators (concat, select, indexed part-select)
``instance.(method)(arg, …)``
  Call a method of a module
``function(args…)``
  Call an internal function
``extcall function(args…)``
  Call an external function (combinational IP)
``Ob~1~0~1~0``, ``|4`d10|``
  Bitset constants (here, the number 10 on 4 bits)
``struct name { field_n := val_n;… }``
  Struct constants
``enum name { member }``
  Enum constants
``#val``
  Lift a Coq value (for example a Coq definition)

For example, the following rule decreases the ``ttl`` field of an ICMP packet:

.. code:: coq

   Definition _decr_icmp_ttl := {{
     let hdr := unpack(struct_t ipv4_header, read0(input)) in
     let valid := Ob~1 in
     match get(hdr, protocol) with
     | enum proto { ICMP } =>
       let t := get(hdr, ttl) in
       if t == |8`d0| then set valid := Ob~0
       else set hdr := subst(hdr, ttl, t - |8`d1|)
     return default: fail
     end;
     write0(output, pack(struct response { valid := valid; value := hdr }))
   }}.

This rule fetches the next instruction in our RV32I core:

.. code:: coq

   Definition fetch := {{
     let pc := read1(pc) in
     write1(pc, pc + |32`d4|);
     toIMem.(MemReq.enq)(struct mem_req {
          byte_en := |4`d0|; (* Load *)
          addr := pc;
          data := |32`d0|
        });
     f2d.(fromFetch.enq)(struct fetch_bookkeeping {
          pc := pc;
          ppc := pc + |32`d4|;
          epoch := read1(epoch)
       })
   }}.

Rules are written in an untyped surface language; to typecheck a rule, use ``tc_action R Sigma rule_body``, or use ``tc_rules`` as shown below.

Schedulers
~~~~~~~~~~

A scheduler defines a priority order on rules: in each cycle rules appear to execute sequentially, and later rules that conflict with earlier ones do not execute (of course, all this is about semantics; the circuits generated by the compiler are (almost entirely) parallel).

A scheduler refers to rules by name, so you need three things:

- A rule name type:

  .. code:: coq

     Inductive rule_name_t :=
       start | step_compute | get_result.

- A scheduler definition:

  .. code:: coq

     Definition scheduler :=
       start |> step_compute |> get_result |> done.

- A mapping from rule names to (typechecked) rules:

  .. code:: coq

     Definition rules :=
       tc_rules R Sigma
         (fun rl =>
          match rl with
          | start => {{ … rule body … }}
          | step_compute => gcd_compute
          | get_result => {{ … rule body … }}
          end).

.. _formal-semantics:

Formal semantics
----------------

The semantics of |koika| programs are given by a reference interpreter written in Coq.  The results computed by this interpreter are the specification of the meaning of each program.

The reference interpreter takes three inputs:

- A program, using the syntax described above

- The initial value of each state element, ``r``

  .. code:: coq

     Definition r (reg: reg_t): R reg :=
       match reg with
       | to_memory st => MemReqFIFO.r st
       | register_file st => Rf.r st
       …
       | pc => Bits.zero
       | epoch => Bits.zero
       end.

- A Coq model of the external IP that you use, if any:

  .. code:: coq

     Definition sigma (fn: ext_fn_t): Sig_denote (Sigma fn) :=
       match fn with
       | custom_adder sz => fun (bs1 bs2: bits sz) => Bits.plus bs1 bs2
       end.

Then you can run your code:

.. code:: coq

   Definition cr := ContextEnv.(create) r.

   (* This computes a log of reads and writes *)
   Definition event_log :=
     tc_compute (interp_scheduler cr sigma rules scheduler).

   (* This computes the new value of each register *)
   Definition interp_result :=
     tc_compute (commit_update cr event_log).

This ``interp_scheduler`` function implements the executable reference semantics of |koika|; it can be used to prove properties about programs, to guarantee that program transformation are correct, or to verify a compiler.

.. _compiler-verification:

Compiler verification
---------------------

In addition to the reference interpreter, we have a verified compiler that targets RTL.  “Verified”, in this context, means that we have a machine-checked proof that the circuits produced by the compiler compute the exact same results as the original programs they were compiled from (the theorem is ``compiler_correct`` in `<coq/CircuitCorrectness.v>`_).

For instance, in the following example, our theorem guarantees that ``circuits_result`` matches ``interp_result`` above:

.. code:: coq

   Definition is_external (r: rule_name_t) :=
     false.

   Definition circuits :=
     compile_scheduler rules is_external collatz.

   Definition circuits_result :=
     tc_compute (interp_circuits empty_sigma circuits (lower_r (ContextEnv.(create) r))).

.. _cuttlesim:

C++ Simulation
--------------

For simulation, debugging, and testing purposes, we have a separate compiler, ``cuttlesim``, which generates C++ models from |koika| designs.  The models are reasonably readable, suitable for debugging with GDB or LLDB, and typically run significantly faster than RTL simulation.  Here is a concrete example, generated from `<examples/gcd_machine.v>`_:

.. code:: c

   bool rule_step_compute() noexcept {
     {
       bits<16> a;
       READ0(step_compute, gcd_a, &a);
       {
         bits<16> b;
         READ0(step_compute, gcd_b, &b);
         if ((a != 16'0_b)) {
           if ((a < b)) {
             WRITE0(step_compute, gcd_b, a);
             WRITE0(step_compute, gcd_a, b);
           } else {
             WRITE0(step_compute, gcd_a, (a - b));
           }
         } else {
           FAIL_FAST(step_compute);
         }
       }
     }

     COMMIT(step_compute);
     return true;
   }

The Makefile generated by ``cuttlec`` contains multiple useful targets that can be used in connection with ``cuttlesim``; for example, coverage statistics (using ``gcov``) can be used to get a detailed picture of which rules of a design tend to fail, and for what reasons, which makes it easy to diagnose e.g. back-pressure due to incorrect pipelining setups.  Additionally, ``cuttlesim`` models can be used to generate value change dumps that can be visualized with `GTKWave <http://gtkwave.sourceforge.net/>`_.

We wrote `a paper about cuttlesim <https://pit-claudel.fr/clement/papers/cuttlesim-ASPLOS21.pdf>`__.

Compilation
-----------

The usual compilation process for programs defined using our Coq EDSL in as follows:

1. Write you program as shown above.
2. Write a *package*, gathering all pieces of your program together; packages are documented in `<coq/Interop.v>`_.
3. Export that package using extraction to OCaml.
4. Compile this package to Verilog, C++, etc. using ``cuttlec``; this invokes the verified compiler to circuits and a thin unverified layer to produce RTL, or separate (unverified) code to produce C++ models and graphs.

Additional topics
=================

.. _makefile:

RTL Simulation, tracing, profiling, etc.
----------------------------------------

Running the ``cuttlec`` with the ``-t all`` flag generates all supported output formats, and a ``Makefile`` with a number of useful targets, including the following (replace ``collatz`` with the name of your design):

* ``make obj_dir/Vcollatz``

  Compile the generated RTL with Verilator.

* ``make gdb``

  Compile the C++ model of your design in debug mode, then run it under GDB.

* ``make collatz.hpp.gcov``

  Generate coverage statistics for the C++ model of your design (this shows which rules firer, how often then fire, and why they fail when they do).

* ``make NCYCLES=25 gtkwave.verilator``

  Compile the generated RTL with Verilator in ``--trace`` mode, then a VCD trace over 25 cycles and open it in GTKWave.

Use ``make help`` in the generated directory to learn more.

Function definitions
--------------------

It is often convenient to define reusable combinational functions separately, as in `this example <examples/rv/RVCore.v>`_:

.. code:: coq

   Definition alu32: UInternalFunction reg_t empty_ext_fn_t := {{
     fun (funct3: bits_t 3) (inst_30: bits_t 1)
         (a: bits_t 32) (b: bits_t 32): bits_t 32 =>
       let shamt := b[Ob~0~0~0~0~0 :+ 5] in
       match funct3 with
       | #funct3_ADD  => if (inst_30 == Ob~1) then a - b else a + b
       | #funct3_SLL  => a << shamt
       | #funct3_SLT  => zeroExtend(a <s b, 32)
       | #funct3_SLTU => zeroExtend(a < b, 32)
       | #funct3_XOR  => a ^ b
       | #funct3_SRL  => if (inst_30 == Ob~1) then a >>> shamt else a >> shamt
       | #funct3_OR   => a || b
       | #funct3_AND  => a && b
       return default: |32`d0|
       end
   }}.

That function would be called by writing ``alu32(fn3, i30, a, b)``.

.. _modularity:

Modularity
----------

Function definitions are best for stateless (combinational) programs.  For stateful code fragments, |koika| has a limited form of method calls.

The following (excerpted from `<examples/conflicts_modular.v>`_) defines a ``Queue32`` module implementing a bypassing FIFO, with methods to dequeue at port 0 and 1 and a method to enqueue at port 0.

.. code:: coq

   Module Import Queue32.
     Inductive reg_t := empty | data.

     Definition R reg :=
       match reg with
       | empty => bits_t 1
       | data => bits_t 32
       end.

     Definition dequeue0: UInternalFunction reg_t empty_ext_fn_t :=
       {{ fun dequeue0 () : bits_t 32 =>
            guard(!read0(empty));
            write0(empty, Ob~1);
            read0(data) }}.

     Definition enqueue0: UInternalFunction reg_t empty_ext_fn_t :=
       {{ fun enqueue0 (val: bits_t 32) : unit_t =>
            guard(read0(empty));
            write0(empty, Ob~0);
            write0(data, val) }}.

     Definition dequeue1: UInternalFunction reg_t empty_ext_fn_t :=
       {{ fun dequeue1 () : bits_t 32 =>
            guard(!read1(empty));
            write1(empty, Ob~1);
            read1(data) }}.
   End Queue32.

Our earlier example of conflicts can then be written thus:

.. code:: coq

   Inductive reg_t :=
   | in0: Queue32.reg_t -> reg_t
   | in1: Queue32.reg_t -> reg_t
   | fifo: Queue32.reg_t -> reg_t
   | out: Queue32.reg_t -> reg_t.

   Inductive rule_name_t := deq0 | deq1 | process.

   Definition R (reg: reg_t) : type :=
     match reg with
     | in0 st => Queue32.R st
     | in1 st => Queue32.R st
     | fifo st => Queue32.R st
     | out st => Queue32.R st
     end.

   Definition urules (rl: rule_name_t) :=
     match rl with
     | deq0 =>
       {{ fifo.(enqueue0)(in0.(dequeue0)()) }}
     | deq1 =>
       {{ fifo.(enqueue0)(in1.(dequeue0)()) }}
     | process =>
       {{ out.(enqueue0)(fifo.(dequeue1)() + |32`d412|) }}
     end.

.. _lispy-verilog:

Machine-friendly input
----------------------

When generating |koika| code from another language, it can be easier to target a format with a simpler syntax than our Coq EDSL.  In that case you can use Lispy Verilog, an alternative syntax for |koika| based on s-expressions.  See the `<examples/>`_ and `<tests/>`_ directories for more information; here is `one example <examples/collatz.lv>`_; the Coq version of the same program is in `<examples/collatz.v>`_:

.. code:: lisp

   ;;; Computing terms of the Collatz sequence (Lispy Verilog version)

   (defun times_three ((v (bits 16))) (bits 16)
     (+ (<< v 1'1) v))

   (module collatz
     (register r0 16'19)

     (rule divide
       (let ((v (read.0 r0))
             (odd (sel v 4'0)))
         (when (not odd)
           (write.0 r0 (lsr v 1'1)))))

     (rule multiply
       (let ((v (read.1 r0))
             (odd (sel v 4'0)))
         (when odd
           (write.1 r0 (+ (times_three v) 16'1)))))

     (scheduler main
       (sequence divide multiply)))

Running on FPGA
---------------

The Makefiles that ``cuttlec`` generates include targets for generating ECP5 and ICE40 bitstreams.  The default ECP5 target is set up for the `ULX3S-85k <https://www.crowdsupply.com/radiona/ulx3s>`__ FPGA.  The default ICE40 target is set up for the `TinyFPGA BX <https://www.crowdsupply.com/tinyfpga/tinyfpga-ax-bx>`__.  Both are reasonably affordable FPGAs (but note that right now the RV32i code does not fit on the TinyFPGA BX).

To run the RISCV5 core on the ULX3S on Ubuntu 20:

- Download a prebuilt ECP5 toolchain from `<https://github.com/YosysHQ/fpga-toolchain/releases>`__.
- Make sure that the trivial example at https://github.com/ulx3s/blink works.
- Run ``make core`` in ``examples/rv`` to compile the RISCV core (other designs should work too, but you'll need to create a custom wrapper in Verilog to map inputs and outputs to your FPGAs pins.
- Run ``make top_ulx3s.bit`` in ``examples/rv/_objects/rv32i.v/`` to generate a bitstream.  You can prefix this command with ``MEM_NAME=integ/morse`` (or any other test program) to load a different memory image into the bitstream.
- Run ``fujprog top_ulx3s.bit`` to flash the FPGA.
- To see the output of ``putchar()``, use a TTY application like ``tio``: ``tio /dev/ttyUSB0`` (the default baud rate is 115200).
  Alternatively, use ``tty -F /dev/ttyUSB0 115200 igncr`` to set up the terminal and then use ``cat /dev/ttyUSB0``.

.. |koika| replace:: Kôika
