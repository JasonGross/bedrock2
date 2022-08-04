Require bedrock2.BasicC64Semantics bedrock2.NotationsCustomEntry.
Import BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Require Import coqutil.Macros.ident_to_string.

Section chacha20.
  Import bedrock2.Syntax Syntax.Coercions NotationsCustomEntry.

  Local Notation "x <<<= n" := (cmd.set (ident_to_string! x) (expr.op bopname.slu (ident_to_string! x) n)) (in custom bedrock_cmd at level 0, x ident, n bigint).
  Local Notation "x ^= e" := (cmd.set (ident_to_string! x) (expr.op bopname.xor (ident_to_string! x) e)) (in custom bedrock_cmd at level 0, x ident, e custom bedrock_expr).
  Local Notation "x += e" := (cmd.set (ident_to_string! x) (expr.op bopname.add (ident_to_string! x) e)) (in custom bedrock_cmd at level 0, x ident, e custom bedrock_expr).

  Definition chacha20_quarter : func :=
    ("chacha20_quarter", (["a";"b";"c";"d"], ["a";"b";"c";"d"], bedrock_func_body:(
      a += b; d ^= a; d <<<= 16;
      c += d; b ^= c; b <<<= 12;
      a += b; d ^= a; d <<<= 8;
      c += d; b ^= c; b <<<= 7
    ))).

  Definition QUARTERROUND (a b c d : String.string) : cmd
    := ltac:(let body := (eval cbv [chacha20_quarter] in (let '(_, (_, _, body)) := chacha20_quarter in body)) in
             lazymatch (eval pattern "a", "b", "c", "d" in body) with
             | ?x "a" "b" "c" "d"
               => let y := (eval cbv beta in (x a b c d)) in
                  exact y
             end).

  Local Notation "'xorout' o x" := (
      let addr := bedrock_expr:(out+coq:(expr.literal(4*o))) in
      bedrock_cmd:(store4($addr, load4($addr)^$(expr.var (ident_to_string! x)))))
      (in custom bedrock_cmd at level 0, o bigint, x ident).

  Definition chacha20_block_separate : func :=
    (* NOTE: I (andreser) don't understand why xorout needs these *)
    let x0  := "x0" in let x1  := "x1" in let x2  := "x2" in let x3  := "x3" in
    let x4  := "x4" in let x5  := "x5" in let x6  := "x6" in let x7  := "x7" in
    let x8  := "x8" in let x9  := "x9" in let x10 := "x10" in let x11 := "x11" in
    let x12 := "x12" in let x13 := "x13" in let x14 := "x14" in let x15 := "x15" in
    ("chacha20_block", (["out"; "key"; "nonce"; "countervalue"], [], bedrock_func_body:(
      x0 = $0x61707865;   x1 = $0x3320646e;   x2 = $0x79622d32;    x3 = $0x6b206574;
      x4 = load4(key);           x5 = load4(key+$4);   x6 = load4(key+$8);    x7 = load4(key+$12);
      x8 = load4(key+$16);  x9 = load4(key+$20); x10 = load4(key+$24);  x11 = load4(key+$28);
      x12 = countervalue;       x13 = load4(nonce);        x14 = load4(nonce+$4); x15 = load4(nonce+$8);
      i = $0; while (i < $10) { i += $1;
        (x0, x4,  x8, x12) = chacha20_quarter( x0, x4, x8,  x12);
        (x1, x5,  x9, x13) = chacha20_quarter( x1, x5, x9,  x13);
        (x2, x6, x10, x14) = chacha20_quarter( x2, x6, x10, x14);
        (x3, x7, x11, x15) = chacha20_quarter( x3, x7, x11, x15);
        (x0, x5, x10, x15) = chacha20_quarter( x0, x5, x10, x15);
        (x1, x6, x11, x12) = chacha20_quarter( x1, x6, x11, x12);
        (x2, x7,  x8, x13) = chacha20_quarter( x2, x7, x8,  x13);
        (x3, x4,  x9, x14) = chacha20_quarter( x3, x4, x9,  x14)
      };
      x0 += $0x61707865;  x1 += $0x3320646e;   x2 += $0x79622d32;    x3 += $0x6b206574;
      x4 += load4(key);          x5 += load4(key+$4);   x6 += load4(key+$8);    x7 += load4(key+$12);
      x8 += load4(key+$16); x9 += load4(key+$20); x10 += load4(key+$24);  x11 += load4(key+$28);
      x12 += countervalue;      x13 += load4(nonce);        x14 += load4(nonce+$4); x15 += load4(nonce+$8);
      xorout  0  x0;   xorout 1 x1; xorout 2   x2;  xorout 3  x3;
      xorout  4  x4;   xorout 5 x5; xorout 6   x6;  xorout 7  x7;
      xorout  8  x8;   xorout 9 x9; xorout 10 x10; xorout 11 x11;
      xorout 12 x12; xorout 13 x13; xorout 14 x14; xorout 15 x15
  ))).

  Local Ltac repquarterround body :=
    lazymatch body with
    | context body[cmd.call [?x1; ?x2; ?x3; ?x4] "chacha20_quarter" [expr.var ?x1; expr.var ?x2; expr.var ?x3; expr.var ?x4] ]
      => let body := context body[QUARTERROUND x1 x2 x3 x4] in
         repquarterround body
    | context body[cmd.call ?ls "chacha20_quarter" ?ls' ]
      => let v := constr:(cmd.call ls "chacha20_quarter" ls') in
         fail 0 "could not replace ""chacha20_quarter"" in" v
    | context["chacha20_quarter"]
      => fail 0 "could not replace ""chacha20_quarter"" in" body
    | _ => body
    end.
  Definition chacha20_block : func :=
    ltac:(let body := (eval cbv delta [chacha20_block_separate] in chacha20_block_separate) in
          let body := repquarterround body in
          exact body).
End chacha20.

(*
Require bedrock2.ToCString.
Example chacha20_block_c_string := Eval vm_compute in
  ToCString.c_module [chacha20_quarter; chacha20_block_separate].
Print chacha20_block_c_string.
*)

From Coq Require Import String.
From Coq Require Import ZArith.ZArith.
From coqutil Require Import Word.Interface Word.Properties Map.Interface.
From coqutil.Word Require Import Naive.
From coqutil.Tactics Require Import letexists eabstract.
From bedrock2 Require Import FE310CSemantics Semantics WeakestPrecondition ProgramLogic Array Scalars Loops.
From bedrock2.Map Require Import Separation SeparationLogic.
From coqutil.Z Require Import Lia.

Local Infix "*" := sep.
Local Infix "*" := sep : type_scope.

Local Existing Instance coqutil.Word.Naive.word.

Instance spec_of_chacha20 : spec_of "chacha20_block" := fun functions =>
  forall outAddr out keyAddr key nonceAddr nonce cval R m t,
    (array scalar32 (word.of_Z 4) outAddr out *
     array scalar32 (word.of_Z 4) keyAddr key *
     array scalar32 (word.of_Z 4) nonceAddr nonce *
     R) m ->
    16 = Z.of_nat (List.length out) ->
    8 = Z.of_nat (List.length key) ->
    3 = Z.of_nat (List.length nonce) ->
    WeakestPrecondition.call functions "chacha20_block" t m [outAddr; keyAddr; nonceAddr; cval]
                             (fun t' m' rets => exists out',
                                  t' = t /\ (array scalar32 (word.of_Z 4) outAddr out' *
                                            array scalar32 (word.of_Z 4) keyAddr key *
                                            array scalar32 (word.of_Z 4) nonceAddr nonce *
                                            R) m' /\ rets = []).

Hint Rewrite
     word.unsigned_of_Z word.signed_of_Z word.of_Z_unsigned word.unsigned_add word.unsigned_sub word.unsigned_opp word.unsigned_or word.unsigned_and word.unsigned_xor word.unsigned_not word.unsigned_ndn word.unsigned_mul word.signed_mulhss word.signed_mulhsu word.unsigned_mulhuu word.unsigned_divu word.signed_divs word.unsigned_modu word.signed_mods word.unsigned_slu word.unsigned_sru word.signed_srs word.unsigned_eqb word.unsigned_ltu word.signed_lts
     using trivial
  : word_laws.

Import BasicC64Semantics. (* for ring *)
Notation "( x , y , .. , z )" := (PrimitivePair.pair.mk .. (PrimitivePair.pair.mk x y) .. z) : core_scope.
    Notation "'dlet' x .. y := v 'in' f" := (dlet.dlet v (fun x => .. (fun y => f) .. ))
                                              (at level 200, x binder, y binder, f at level 200, format "'dlet'  x .. y  :=  v  'in' '//' f").

    Import NotationsCustomEntry.
Goal   forall
    functions : list
                  (prod string
                     (prod (prod (list string) (list string)) Syntax.cmd.cmd)),
  let c := bedrock_func_body:(
      $"x4" = $(Syntax.expr.var "x4") ^ $(Syntax.expr.var "x8");
      $"x4" = $(Syntax.expr.var "x4") << $(Syntax.expr.literal 7)) in
  let c0 := bedrock_func_body:(
      $"x8" = $(Syntax.expr.var "x8") + $(Syntax.expr.var "x12");
      $c) in
  let c1 := bedrock_func_body:(
      $"x12" = $(Syntax.expr.var "x12") << $(Syntax.expr.literal 8);
      $c0) in
  let c2 := bedrock_func_body:(
      $"x12" = $(Syntax.expr.var "x12") ^ $(Syntax.expr.var "x0");
      $c1) in
  let c3 := bedrock_func_body:(
      $"x0" = $(Syntax.expr.var "x0") + $(Syntax.expr.var "x4");
      $c2) in
  let c4 := bedrock_func_body:(
      $"x4" = $(Syntax.expr.var "x4") << $(Syntax.expr.literal 12);
      $c3) in
  let c5 := bedrock_func_body:(
      $"x4" = $(Syntax.expr.var "x4") ^ $(Syntax.expr.var "x8");
      $c4) in
  let c6 := bedrock_func_body:(
      $"x8" = $(Syntax.expr.var "x8") + $(Syntax.expr.var "x12");
      $c5) in
  let c7 := bedrock_func_body:(
      $"x12" = $(Syntax.expr.var "x12") << $(Syntax.expr.literal 16);
      $c6) in
  let c8 := bedrock_func_body:(
      $"x12" = $(Syntax.expr.var "x12") ^ $(Syntax.expr.var "x0");
      $c7) in
  let c9 := bedrock_func_body:(
      $"x0" = $(Syntax.expr.var "x0") + $(Syntax.expr.var "x4");
      $c8) in
  let c10 := bedrock_func_body:(
      $"x5" = $(Syntax.expr.var "x5") ^ $(Syntax.expr.var "x9");
      $"x5" = $(Syntax.expr.var "x5") << $(Syntax.expr.literal 7)) in
  let c11 := bedrock_func_body:(
      $"x9" = $(Syntax.expr.var "x9") + $(Syntax.expr.var "x13");
      $c10) in
  let c12 := bedrock_func_body:(
      $"x13" = $(Syntax.expr.var "x13") << $(Syntax.expr.literal 8);
      $c11) in
  let c13 := bedrock_func_body:(
      $"x13" = $(Syntax.expr.var "x13") ^ $(Syntax.expr.var "x1");
      $c12) in
  let c14 := bedrock_func_body:(
      $"x1" = $(Syntax.expr.var "x1") + $(Syntax.expr.var "x5");
      $c13) in
  let c15 := bedrock_func_body:(
      $"x5" = $(Syntax.expr.var "x5") << $(Syntax.expr.literal 12);
      $c14) in
  let c16 := bedrock_func_body:(
      $"x5" = $(Syntax.expr.var "x5") ^ $(Syntax.expr.var "x9");
      $c15) in
  let c17 := bedrock_func_body:(
      $"x9" = $(Syntax.expr.var "x9") + $(Syntax.expr.var "x13");
      $c16) in
  let c18 := bedrock_func_body:(
      $"x13" = $(Syntax.expr.var "x13") << $(Syntax.expr.literal 16);
      $c17) in
  let c19 := bedrock_func_body:(
      $"x13" = $(Syntax.expr.var "x13") ^ $(Syntax.expr.var "x1");
      $c18) in
  let c20 := bedrock_func_body:(
      $"x1" = $(Syntax.expr.var "x1") + $(Syntax.expr.var "x5");
      $c19) in
  let c21 := bedrock_func_body:(
      $"x6" = $(Syntax.expr.var "x6") ^ $(Syntax.expr.var "x10");
      $"x6" = $(Syntax.expr.var "x6") << $(Syntax.expr.literal 7)) in
  let c22 := bedrock_func_body:(
      $"x10" = $(Syntax.expr.var "x10") + $(Syntax.expr.var "x14");
      $c21) in
  let c23 := bedrock_func_body:(
      $"x14" = $(Syntax.expr.var "x14") << $(Syntax.expr.literal 8);
      $c22) in
  let c24 := bedrock_func_body:(
      $"x14" = $(Syntax.expr.var "x14") ^ $(Syntax.expr.var "x2");
      $c23) in
  let c25 := bedrock_func_body:(
      $"x2" = $(Syntax.expr.var "x2") + $(Syntax.expr.var "x6");
      $c24) in
  let c26 := bedrock_func_body:(
      $"x6" = $(Syntax.expr.var "x6") << $(Syntax.expr.literal 12);
      $c25) in
  let c27 := bedrock_func_body:(
      $"x6" = $(Syntax.expr.var "x6") ^ $(Syntax.expr.var "x10");
      $c26) in
  let c28 := bedrock_func_body:(
      $"x10" = $(Syntax.expr.var "x10") + $(Syntax.expr.var "x14");
      $c27) in
  let c29 := bedrock_func_body:(
      $"x14" = $(Syntax.expr.var "x14") << $(Syntax.expr.literal 16);
      $c28) in
  let c30 := bedrock_func_body:(
      $"x14" = $(Syntax.expr.var "x14") ^ $(Syntax.expr.var "x2");
      $c29) in
  let c31 := bedrock_func_body:(
      $"x2" = $(Syntax.expr.var "x2") + $(Syntax.expr.var "x6");
      $c30) in
  let c32 := bedrock_func_body:(
      $"x7" = $(Syntax.expr.var "x7") ^ $(Syntax.expr.var "x11");
      $"x7" = $(Syntax.expr.var "x7") << $(Syntax.expr.literal 7)) in
  let c33 := bedrock_func_body:(
      $"x11" = $(Syntax.expr.var "x11") + $(Syntax.expr.var "x15");
      $c32) in
  let c34 := bedrock_func_body:(
      $"x15" = $(Syntax.expr.var "x15") << $(Syntax.expr.literal 8);
      $c33) in
  let c35 := bedrock_func_body:(
      $"x15" = $(Syntax.expr.var "x15") ^ $(Syntax.expr.var "x3");
      $c34) in
  let c36 := bedrock_func_body:(
      $"x3" = $(Syntax.expr.var "x3") + $(Syntax.expr.var "x7");
      $c35) in
  let c37 := bedrock_func_body:(
      $"x7" = $(Syntax.expr.var "x7") << $(Syntax.expr.literal 12);
      $c36) in
  let c38 := bedrock_func_body:(
      $"x7" = $(Syntax.expr.var "x7") ^ $(Syntax.expr.var "x11");
      $c37) in
  let c39 := bedrock_func_body:(
      $"x11" = $(Syntax.expr.var "x11") + $(Syntax.expr.var "x15");
      $c38) in
  let c40 := bedrock_func_body:(
      $"x15" = $(Syntax.expr.var "x15") << $(Syntax.expr.literal 16);
      $c39) in
  let c41 := bedrock_func_body:(
      $"x15" = $(Syntax.expr.var "x15") ^ $(Syntax.expr.var "x3");
      $c40) in
  let c42 := bedrock_func_body:(
      $"x3" = $(Syntax.expr.var "x3") + $(Syntax.expr.var "x7");
      $c41) in
  let c43 := bedrock_func_body:(
      $"x5" = $(Syntax.expr.var "x5") ^ $(Syntax.expr.var "x10");
      $"x5" = $(Syntax.expr.var "x5") << $(Syntax.expr.literal 7)) in
  let c44 := bedrock_func_body:(
      $"x10" = $(Syntax.expr.var "x10") + $(Syntax.expr.var "x15");
      $c43) in
  let c45 := bedrock_func_body:(
      $"x15" = $(Syntax.expr.var "x15") << $(Syntax.expr.literal 8);
      $c44) in
  let c46 := bedrock_func_body:(
      $"x15" = $(Syntax.expr.var "x15") ^ $(Syntax.expr.var "x0");
      $c45) in
  let c47 := bedrock_func_body:(
      $"x0" = $(Syntax.expr.var "x0") + $(Syntax.expr.var "x5");
      $c46) in
  let c48 := bedrock_func_body:(
      $"x5" = $(Syntax.expr.var "x5") << $(Syntax.expr.literal 12);
      $c47) in
  let c49 := bedrock_func_body:(
      $"x5" = $(Syntax.expr.var "x5") ^ $(Syntax.expr.var "x10");
      $c48) in
  let c50 := bedrock_func_body:(
      $"x10" = $(Syntax.expr.var "x10") + $(Syntax.expr.var "x15");
      $c49) in
  let c51 := bedrock_func_body:(
      $"x15" = $(Syntax.expr.var "x15") << $(Syntax.expr.literal 16);
      $c50) in
  let c52 := bedrock_func_body:(
      $"x15" = $(Syntax.expr.var "x15") ^ $(Syntax.expr.var "x0");
      $c51) in
  let c53 := bedrock_func_body:(
      $"x0" = $(Syntax.expr.var "x0") + $(Syntax.expr.var "x5");
      $c52) in
  let c54 := bedrock_func_body:(
      $"x6" = $(Syntax.expr.var "x6") ^ $(Syntax.expr.var "x11");
      $"x6" = $(Syntax.expr.var "x6") << $(Syntax.expr.literal 7)) in
  let c55 := bedrock_func_body:(
      $"x11" = $(Syntax.expr.var "x11") + $(Syntax.expr.var "x12");
      $c54) in
  let c56 := bedrock_func_body:(
      $"x12" = $(Syntax.expr.var "x12") << $(Syntax.expr.literal 8);
      $c55) in
  let c57 := bedrock_func_body:(
      $"x12" = $(Syntax.expr.var "x12") ^ $(Syntax.expr.var "x1");
      $c56) in
  let c58 := bedrock_func_body:(
      $"x1" = $(Syntax.expr.var "x1") + $(Syntax.expr.var "x6");
      $c57) in
  let c59 := bedrock_func_body:(
      $"x6" = $(Syntax.expr.var "x6") << $(Syntax.expr.literal 12);
      $c58) in
  let c60 := bedrock_func_body:(
      $"x6" = $(Syntax.expr.var "x6") ^ $(Syntax.expr.var "x11");
      $c59) in
  let c61 := bedrock_func_body:(
      $"x11" = $(Syntax.expr.var "x11") + $(Syntax.expr.var "x12");
      $c60) in
  let c62 := bedrock_func_body:(
      $"x12" = $(Syntax.expr.var "x12") << $(Syntax.expr.literal 16);
      $c61) in
  let c63 := bedrock_func_body:(
      $"x12" = $(Syntax.expr.var "x12") ^ $(Syntax.expr.var "x1");
      $c62) in
  let c64 := bedrock_func_body:(
      $"x1" = $(Syntax.expr.var "x1") + $(Syntax.expr.var "x6");
      $c63) in
  let c65 := bedrock_func_body:(
      $"x7" = $(Syntax.expr.var "x7") ^ $(Syntax.expr.var "x8");
      $"x7" = $(Syntax.expr.var "x7") << $(Syntax.expr.literal 7)) in
  let c66 := bedrock_func_body:(
      $"x8" = $(Syntax.expr.var "x8") + $(Syntax.expr.var "x13");
      $c65) in
  let c67 := bedrock_func_body:(
      $"x13" = $(Syntax.expr.var "x13") << $(Syntax.expr.literal 8);
      $c66) in
  let c68 := bedrock_func_body:(
      $"x13" = $(Syntax.expr.var "x13") ^ $(Syntax.expr.var "x2");
      $c67) in
  let c69 := bedrock_func_body:(
      $"x2" = $(Syntax.expr.var "x2") + $(Syntax.expr.var "x7");
      $c68) in
  let c70 := bedrock_func_body:(
      $"x7" = $(Syntax.expr.var "x7") << $(Syntax.expr.literal 12);
      $c69) in
  let c71 := bedrock_func_body:(
      $"x7" = $(Syntax.expr.var "x7") ^ $(Syntax.expr.var "x8");
      $c70) in
  let c72 := bedrock_func_body:(
      $"x8" = $(Syntax.expr.var "x8") + $(Syntax.expr.var "x13");
      $c71) in
  let c73 := bedrock_func_body:(
      $"x13" = $(Syntax.expr.var "x13") << $(Syntax.expr.literal 16);
      $c72) in
  let c74 := bedrock_func_body:(
      $"x13" = $(Syntax.expr.var "x13") ^ $(Syntax.expr.var "x2");
      $c73) in
  let c75 := bedrock_func_body:(
      $"x2" = $(Syntax.expr.var "x2") + $(Syntax.expr.var "x7");
      $c74) in
  let c76 := bedrock_func_body:(
      $"x4" = $(Syntax.expr.var "x4") ^ $(Syntax.expr.var "x9");
      $"x4" = $(Syntax.expr.var "x4") << $(Syntax.expr.literal 7)) in
  let c77 := bedrock_func_body:(
      $"x9" = $(Syntax.expr.var "x9") + $(Syntax.expr.var "x14");
      $c76) in
  let c78 := bedrock_func_body:(
      $"x14" = $(Syntax.expr.var "x14") << $(Syntax.expr.literal 8);
      $c77) in
  let c79 := bedrock_func_body:(
      $"x14" = $(Syntax.expr.var "x14") ^ $(Syntax.expr.var "x3");
      $c78) in
  let c80 := bedrock_func_body:(
      $"x3" = $(Syntax.expr.var "x3") + $(Syntax.expr.var "x4");
      $c79) in
  let c81 := bedrock_func_body:(
      $"x4" = $(Syntax.expr.var "x4") << $(Syntax.expr.literal 12);
      $c80) in
  let c82 := bedrock_func_body:(
      $"x4" = $(Syntax.expr.var "x4") ^ $(Syntax.expr.var "x9");
      $c81) in
  let c83 := bedrock_func_body:(
      $"x9" = $(Syntax.expr.var "x9") + $(Syntax.expr.var "x14");
      $c82) in
  let c84 := bedrock_func_body:(
      $"x14" = $(Syntax.expr.var "x14") << $(Syntax.expr.literal 16);
      $c83) in
  let c85 := bedrock_func_body:(
      $"x14" = $(Syntax.expr.var "x14") ^ $(Syntax.expr.var "x3");
      $c84) in
  let c86 := bedrock_func_body:(
      $"x3" = $(Syntax.expr.var "x3") + $(Syntax.expr.var "x4");
      $c85) in
  let c87 := bedrock_func_body:($c75;
                                $c86) in
  let c88 := bedrock_func_body:($c64;
                                $c87) in
  let c89 := bedrock_func_body:($c53;
                                $c88) in
  let c90 := bedrock_func_body:($c42;
                                $c89) in
  let c91 := bedrock_func_body:($c31;
                                $c90) in
  let c92 := bedrock_func_body:($c20;
                                $c91) in
  let c93 := bedrock_func_body:($c9;
                                $c92) in
  let c94 := bedrock_func_body:(
      $"i" = $(Syntax.expr.var "i") + $(Syntax.expr.literal 1);
      $c93) in
  forall
    (outAddr r r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
     r14 : @word.rep 64 word) (out : list (@word.rep 64 word))
    (keyAddr r15 r16 r17 r18 r19 r20 r21 r22 : @word.rep 64 word)
    (key : list (@word.rep 64 word)) (nonceAddr r23 r24 r25 : @word.rep 64 word)
    (nonce : list (@word.rep 64 word)),
  @word.rep 64 word ->
  forall (R : @map.rep (@word.rep 64 word) Init.Byte.byte mem -> Prop)
    (m : @map.rep (@word.rep 64 word) Init.Byte.byte mem),
  ((@scalar32 64 word mem outAddr r *
    (@scalar32 64 word mem (@word.add 64 word outAddr (@word.of_Z 64 word 4)) r0 *
     (@scalar32 64 word mem (@word.add 64 word outAddr (@word.of_Z 64 word 8)) r1 *
      (@scalar32 64 word mem (@word.add 64 word outAddr (@word.of_Z 64 word 12)) r2 *
       (@scalar32 64 word mem (@word.add 64 word outAddr (@word.of_Z 64 word 16))
          r3 *
        (@scalar32 64 word mem (@word.add 64 word outAddr (@word.of_Z 64 word 20))
           r4 *
         (@scalar32 64 word mem (@word.add 64 word outAddr (@word.of_Z 64 word 24))
            r5 *
          (@scalar32 64 word mem
             (@word.add 64 word outAddr (@word.of_Z 64 word 28)) r6 *
           (@scalar32 64 word mem
              (@word.add 64 word outAddr (@word.of_Z 64 word 32)) r7 *
            (@scalar32 64 word mem
               (@word.add 64 word outAddr (@word.of_Z 64 word 36)) r8 *
             (@scalar32 64 word mem
                (@word.add 64 word outAddr (@word.of_Z 64 word 40)) r9 *
              (@scalar32 64 word mem
                 (@word.add 64 word outAddr (@word.of_Z 64 word 44)) r10 *
               (@scalar32 64 word mem
                  (@word.add 64 word outAddr (@word.of_Z 64 word 48)) r11 *
                (@scalar32 64 word mem
                   (@word.add 64 word outAddr (@word.of_Z 64 word 52)) r12 *
                 (@scalar32 64 word mem
                    (@word.add 64 word outAddr (@word.of_Z 64 word 56)) r13 *
                  (@scalar32 64 word mem
                     (@word.add 64 word outAddr (@word.of_Z 64 word 60)) r14 *
                   @array 64 word Init.Byte.byte mem (@word.rep 64 word)
                     (@scalar32 64 word mem) (@word.of_Z 64 word 4)
                     (@word.add 64 word outAddr (@word.of_Z 64 word 64)) out))))))))))))))) *
    (@scalar32 64 word mem keyAddr r15 *
     (@scalar32 64 word mem (@word.add 64 word keyAddr (@word.of_Z 64 word 4)) r16 *
      (@scalar32 64 word mem (@word.add 64 word keyAddr (@word.of_Z 64 word 8)) r17 *
       (@scalar32 64 word mem (@word.add 64 word keyAddr (@word.of_Z 64 word 12))
          r18 *
        (@scalar32 64 word mem (@word.add 64 word keyAddr (@word.of_Z 64 word 16))
           r19 *
         (@scalar32 64 word mem (@word.add 64 word keyAddr (@word.of_Z 64 word 20))
            r20 *
          (@scalar32 64 word mem
             (@word.add 64 word keyAddr (@word.of_Z 64 word 24)) r21 *
           (@scalar32 64 word mem
              (@word.add 64 word keyAddr (@word.of_Z 64 word 28)) r22 *
            @array 64 word Init.Byte.byte mem (@word.rep 64 word)
              (@scalar32 64 word mem) (@word.of_Z 64 word 4)
              (@word.add 64 word keyAddr (@word.of_Z 64 word 32)) key)))))))) *
    (@scalar32 64 word mem nonceAddr r23 *
     (@scalar32 64 word mem (@word.add 64 word nonceAddr (@word.of_Z 64 word 4))
        r24 *
      (@scalar32 64 word mem (@word.add 64 word nonceAddr (@word.of_Z 64 word 8))
         r25 *
       @array 64 word Init.Byte.byte mem (@word.rep 64 word)
         (@scalar32 64 word mem) (@word.of_Z 64 word 4)
         (@word.add 64 word nonceAddr (@word.of_Z 64 word 12)) nonce))))%type * R)
    m ->
  16 =
  Z.of_nat
    (S
       (S
          (S
             (S
                (S
                   (S
                      (S
                         (S
                            (S
                               (S
                                  (S
                                     (S
                                        (S
                                           (S
                                              (S
                                                 (S
                                                    (@Datatypes.length
                                                      (@word.rep 64 word) out))))))))))))))))) ->
  8 =
  Z.of_nat
    (S (S (S (S (S (S (S (S (@Datatypes.length (@word.rep 64 word) key))))))))) ->
  3 = Z.of_nat (S (S (S (@Datatypes.length (@word.rep 64 word) nonce)))) ->
  let x0 := @word.of_Z 64 word 1634760805 in
  let x1 := @word.of_Z 64 word 857760878 in
  let x2 := @word.of_Z 64 word 2036477234 in
  let x3 := @word.of_Z 64 word 1797285236 in
  let x4 := @truncate_word 64 word Syntax.access_size.four r15 in
  let x5 := @truncate_word 64 word Syntax.access_size.four r16 in
  let x6 := @truncate_word 64 word Syntax.access_size.four r17 in
  let x7 := @truncate_word 64 word Syntax.access_size.four r18 in
  let x8 := @truncate_word 64 word Syntax.access_size.four r19 in
  let x9 := @truncate_word 64 word Syntax.access_size.four r20 in
  let x10 := @truncate_word 64 word Syntax.access_size.four r21 in
  let x11 := @truncate_word 64 word Syntax.access_size.four r22 in
  let x13 := @truncate_word 64 word Syntax.access_size.four r23 in
  let x14 := @truncate_word 64 word Syntax.access_size.four r24 in
  let x15 := @truncate_word 64 word Syntax.access_size.four r25 in
  let i := @word.of_Z 64 word 0 in
  let Hsep :=
    (@scalar32 64 word mem outAddr r *
     (@scalar32 64 word mem (@word.add 64 word outAddr (@word.of_Z 64 word 4)) r0 *
      (@scalar32 64 word mem (@word.add 64 word outAddr (@word.of_Z 64 word 8)) r1 *
       (@scalar32 64 word mem (@word.add 64 word outAddr (@word.of_Z 64 word 12))
          r2 *
        (@scalar32 64 word mem (@word.add 64 word outAddr (@word.of_Z 64 word 16))
           r3 *
         (@scalar32 64 word mem (@word.add 64 word outAddr (@word.of_Z 64 word 20))
            r4 *
          (@scalar32 64 word mem
             (@word.add 64 word outAddr (@word.of_Z 64 word 24)) r5 *
           (@scalar32 64 word mem
              (@word.add 64 word outAddr (@word.of_Z 64 word 28)) r6 *
            (@scalar32 64 word mem
               (@word.add 64 word outAddr (@word.of_Z 64 word 32)) r7 *
             (@scalar32 64 word mem
                (@word.add 64 word outAddr (@word.of_Z 64 word 36)) r8 *
              (@scalar32 64 word mem
                 (@word.add 64 word outAddr (@word.of_Z 64 word 40)) r9 *
               (@scalar32 64 word mem
                  (@word.add 64 word outAddr (@word.of_Z 64 word 44)) r10 *
                (@scalar32 64 word mem
                   (@word.add 64 word outAddr (@word.of_Z 64 word 48)) r11 *
                 (@scalar32 64 word mem
                    (@word.add 64 word outAddr (@word.of_Z 64 word 52)) r12 *
                  (@scalar32 64 word mem
                     (@word.add 64 word outAddr (@word.of_Z 64 word 56)) r13 *
                   (@scalar32 64 word mem
                      (@word.add 64 word outAddr (@word.of_Z 64 word 60)) r14 *
                    @array 64 word Init.Byte.byte mem (@word.rep 64 word)
                      (@scalar32 64 word mem) (@word.of_Z 64 word 4)
                      (@word.add 64 word outAddr (@word.of_Z 64 word 64)) out))))))))))))))) *
     (@scalar32 64 word mem keyAddr r15 *
      (@scalar32 64 word mem (@word.add 64 word keyAddr (@word.of_Z 64 word 4)) r16 *
       (@scalar32 64 word mem (@word.add 64 word keyAddr (@word.of_Z 64 word 8))
          r17 *
        (@scalar32 64 word mem (@word.add 64 word keyAddr (@word.of_Z 64 word 12))
           r18 *
         (@scalar32 64 word mem (@word.add 64 word keyAddr (@word.of_Z 64 word 16))
            r19 *
          (@scalar32 64 word mem
             (@word.add 64 word keyAddr (@word.of_Z 64 word 20)) r20 *
           (@scalar32 64 word mem
              (@word.add 64 word keyAddr (@word.of_Z 64 word 24)) r21 *
            (@scalar32 64 word mem
               (@word.add 64 word keyAddr (@word.of_Z 64 word 28)) r22 *
             @array 64 word Init.Byte.byte mem (@word.rep 64 word)
               (@scalar32 64 word mem) (@word.of_Z 64 word 4)
               (@word.add 64 word keyAddr (@word.of_Z 64 word 32)) key)))))))) *
     (@scalar32 64 word mem nonceAddr r23 *
      (@scalar32 64 word mem (@word.add 64 word nonceAddr (@word.of_Z 64 word 4))
         r24 *
       (@scalar32 64 word mem (@word.add 64 word nonceAddr (@word.of_Z 64 word 8))
          r25 *
        @array 64 word Init.Byte.byte mem (@word.rep 64 word)
          (@scalar32 64 word mem) (@word.of_Z 64 word 4)
          (@word.add 64 word nonceAddr (@word.of_Z 64 word 12)) nonce))) * R)%type
    in
  forall (v : nat) (t : @trace 64 Bitwidth64.BW64 word mem)
    (m0 : @map.rep (@word.rep 64 word) Init.Byte.byte mem)
    (x x12 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33
     x34 : @word.rep 64 word),
  let localsmap :=
    @reconstruct 64 word locals
      ["i"; "out"; "key"; "nonce"; "countervalue"; "x0"; "x1"; "x2"; "x3"; "x4";
      "x5"; "x6"; "x7"; "x8"; "x9"; "x10"; "x11"; "x12"; "x13"; "x14"; "x15"]
      (x,
      (x12,
      (x16,
      (x17,
      (x18,
      (x19,
      (x20,
      (x21,
      (x22,
      (x23,
      (x24,
      (x25, (x26, (x27, (x28, (x29, (x30, (x31, (x32, (x33, (x34, tt)))))))))))))))))))))
    in
  Hsep m0 ->
  @word.unsigned 64 word x = 10 - Z.of_nat v ->
  (v <= 10)%nat ->
  let br :=
    if @word.ltu 64 word x (@word.of_Z 64 word 10)
    then @word.of_Z 64 word 1
    else @word.of_Z 64 word 0 in
  @word.unsigned 64 word br <> 0 ->
  @cmd 64 Bitwidth64.BW64 word mem locals ext_spec
    (@call 64 Bitwidth64.BW64 word mem locals ext_spec functions) c94 t m0
    localsmap
    (fun (t' : @trace 64 Bitwidth64.BW64 word mem)
       (m' : @map.rep (@word.rep 64 word) Init.Byte.byte mem)
       (localsmap' : @map.rep string (@word.rep 64 word) locals) =>
     @Markers.unique Prop
       (@Markers.left Prop
          (exists
             x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51
              x52 x53 x54 x55 : @word.rep 64 word,
             @Markers.split Prop
               (@enforce 64 word locals
                  ["i"; "out"; "key"; "nonce"; "countervalue"; "x0"; "x1"; "x2";
                  "x3"; "x4"; "x5"; "x6"; "x7"; "x8"; "x9"; "x10"; "x11"; "x12";
                  "x13"; "x14"; "x15"]
                  (x35,
                  (x36,
                  (x37,
                  (x38,
                  (x39,
                  (x40,
                  (x41,
                  (x42,
                  (x43,
                  (x44,
                  (x45,
                  (x46,
                  (x47, (x48, (x49, (x50, (x51, (x52, (x53, (x54, (x55, tt)))))))))))))))))))))
                  localsmap' /\
                @Markers.right Prop
                  (@Markers.unique Prop
                     (@Markers.left Prop
                        (exists v' : nat,
                           @Markers.split Prop
                             ((Hsep m' /\
                               @word.unsigned 64 word x35 = 10 - Z.of_nat v' /\
                               (v' <= 10)%nat) /\
                              @Markers.right Prop
                                (@Markers.split Prop
                                   ((v' < v)%nat /\
                                    (forall
                                       (T : @trace 64 Bitwidth64.BW64 word mem)
                                       (M : @map.rep (@word.rep 64 word)
                                              Init.Byte.byte mem),
                                     @word.rep 64 word ->
                                     forall x57 x58 x59 x60 : @word.rep 64 word,
                                     @word.rep 64 word ->
                                     @word.rep 64 word ->
                                     @word.rep 64 word ->
                                     @word.rep 64 word ->
                                     @word.rep 64 word ->
                                     @word.rep 64 word ->
                                     @word.rep 64 word ->
                                     @word.rep 64 word ->
                                     @word.rep 64 word ->
                                     @word.rep 64 word ->
                                     @word.rep 64 word ->
                                     @word.rep 64 word ->
                                     @word.rep 64 word ->
                                     @word.rep 64 word ->
                                     @word.rep 64 word ->
                                     @word.rep 64 word ->
                                     T = t' /\
                                     x57 = x36 /\
                                     x58 = x37 /\ x59 = x38 /\ x60 = x39 /\ Hsep M ->
                                     T = t /\
                                     x57 = x12 /\
                                     x58 = x16 /\ x59 = x17 /\ x60 = x18 /\ Hsep M))))))))))).
intros.
    repeat match goal with H : Syntax.cmd.cmd |- _ => subst H end.
    repeat first [ match goal with
                   | [ |- ?ev = ?v :> ?T ]
                     => let ev' := rdelta.rdelta ev in is_evar ev'; change ev with ev'; instantiate(1:=v); reflexivity
                   | [ |- ?x = @Some ?T ?ev ]
                     => is_evar ev;
                        first [ instantiate (1:=match x return match x with Some _ => T | None => unit end with
                                                | Some v => v
                                                | None => tt
                                                end <: T); reflexivity
                              | fail 3 ]
                   end
                 | let v :=
                     match goal with
                     | |- @eq _ (@map.get string (@word.rep _ _) _ _ _) (@Some _ ?v) => v
                     end
                   in
                   tryif is_evar v then fail else
                     (let v' := rdelta.rdelta v in
                      is_evar v'; change v with v')
                 | match goal with
                   | [ |- exists _, _ /\ _ ] => letexists _; split
                   | [ |- dlet x := ?y in ?f ] => change (let x := y in f); intro
                   end
                 | progress (unfold1_cmd_goal; cbv beta match delta [cmd_body])
                 | progress (unfold1_expr_goal; cbv beta match delta [expr_body])
                 | progress cbv [dexpr expr get expr_body literal]
                 | progress cbn [interp_binop] ].
    { lazymatch goal with
      | [ |- ?x = @Some ?T ?ev ]
        => is_evar ev;
           transitivity (@Some T (match x return match x with Some _ => T | None => unit end with
                                  | Some v => v
                                  | None => tt
                                  end <: T))
      end.
      (* Error: Conversion test raised an anomaly:
Anomaly "File "kernel/vconv.ml", line 199, characters 18-24: Assertion failed."
Please report at http://coq.inria.fr/bugs/.
*)
    (*unshelve (do 100 straightline); shelve_unifiable.
    Optimize Proof.*)
    all: cbn [interp_binop].
    all: repeat first [ straightline_cleanup | straightline_unfold ].
    straightline_split
    | straightline_split_refl | straightline_split ].
    straightline_
    Time all: match goal with
              | [ |- ?ev = ?v :> ?T ]
                => is_evar ev; instantiate(1:=v); reflexivity
              | _ => idtac
end.
    all: try let v :=
     match goal with
     | |- @eq _ (@map.get string (@word.rep _ _) _ _ _) (@Some _ ?v) => v
     end
    in
    let v' := rdelta.rdelta v in
    is_evar v'; change v with v'.
    all: [ > match goal with
             | [ |- ?x = @Some ?T ?ev ]
               => is_evar ev;
                  try (instantiate (1:=match x return match x with Some _ => T | None => unit end with
                                       | Some v => v
                                       | None => tt
                                       end <: T); reflexivity)
             | _ => idtac
             end .. | ].
    { lazymatch goal with
      | [ |- ?x = @Some ?T ?ev ]
        => is_evar ev;
           transitivity (@Some T (match x return match x with Some _ => T | None => unit end with
                                  | Some v => v
                                  | None => tt
                                  end <: T))
      end.
      | _ => idtac
         end.

Lemma chacha20_ok : program_logic_goal_for_function! chacha20_block.
Proof.
  straightline.
  repeat (destruct out; [cbn in H0; congruence |]).
  repeat (destruct key; [cbn in H1; congruence |]).
  repeat (destruct nonce; [cbn in H2; congruence |]).
  cbn [array word.add word.of_Z] in H.
  Local Ltac word_add_trans_one addr :=
    match goal with
    | [ H : context[@word.add _ ?w (word.add addr ?x) ?y] |- _ ] =>
      replace (@word.add _ w (word.add addr x) y) with (@word.add _ w addr (word.add x y)) in H by ring
    end.
  Local Ltac word_add_trans addr :=
    repeat word_add_trans_one addr.
  word_add_trans outAddr.
  word_add_trans keyAddr.
  word_add_trans nonceAddr.
  repeat match goal with
         | [ H : context[@word.add _ ?w (word.of_Z ?x) (word.of_Z ?y)] |- _ ] =>
           let z := eval cbv in (x + y) in
               change (@word.add _ w (word.of_Z x) (word.of_Z y)) with (@word.of_Z _ w z) in H
         end.
  repeat straightline.
  subst c95.
  match type of H with
  | ?f m => set (Hsep := f)
  end.
  refine (tailrec (HList.polymorphic_list.nil) ("i"::"out"::"key"::"nonce"::"countervalue"::"x0"::"x1"::"x2"::"x3"::"x4"::"x5"::"x6"::"x7"::"x8"::"x9"::"x10"::"x11"::"x12"::"x13"::"x14"::"x15"::nil)%list%string (fun l t m i out key nonce cval _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => PrimitivePair.pair.mk (Hsep m /\ word.unsigned i = 10 - Z.of_nat l /\ (l <= 10)%nat) (fun T M I OUT KEY NONCE CVAL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => T = t /\ OUT = out /\ KEY = key /\ NONCE = nonce /\ CVAL = cval /\ Hsep M)) lt _ _ _ _ _);
    cbn [reconstruct map.putmany_of_list HList.tuple.to_list
         HList.hlist.foralls HList.tuple.foralls
         HList.hlist.existss HList.tuple.existss
         HList.hlist.apply  HList.tuple.apply
         HList.hlist
         List.repeat Datatypes.length
         HList.polymorphic_list.repeat HList.polymorphic_list.length
         PrimitivePair.pair._1 PrimitivePair.pair._2] in *.

  { repeat straightline. }
  { exact lt_wf. }
  { split; [| split].
    { subst Hsep.
      ecancel_assumption. }
    { subst i.
      rewrite word.unsigned_of_Z.
      cbv [word.wrap].
      rewrite Zmod_0_l.
      match goal with
      | [ |- _ = _ - Z.of_nat ?n ] =>
        unify n (10%nat)
      end.
      reflexivity.
    }
    { blia. }
  }
  { Notation "( x , y , .. , z )" := (PrimitivePair.pair.mk .. (PrimitivePair.pair.mk x y) .. z) : core_scope.
    Notation "'dlet' x .. y := v 'in' f" := (dlet.dlet v (fun x => .. (fun y => f) .. ))
                                              (at level 200, x binder, y binder, f at level 200, format "'dlet'  x .. y  :=  v  'in' '//' f").
    Set Printing Depth 1000000.
    repeat match goal with |- forall _, _ => straightline end.
    Time repeat (straightline; []).
    straightline; [ | solve [ intuition ] ].
    straightline.
    Import NotationsCustomEntry.
    Ltac straightline_subst :=
      idtac;
      lazymatch goal with
      | [ |- @cmd _ _ _ _ _ _ _ (Syntax.cmd.set ?s ?e) _ _ _ ?post ]
        => fail
      | [ |- @cmd _ _ _ _ _ _ _ ?c _ _ _ ?post ]
        => time "unfold"
                (idtac;
                 let c := eval hnf in c in
                   lazymatch c with
                   | Syntax.cmd.while _ _ => fail
                   | Syntax.cmd.cond _ _ _ => fail
                   | Syntax.cmd.interact _ _ _ => fail
                   | _ => idtac
                   end; unfold1_cmd_goal; cbv beta match delta [cmd_body])
      end.
    Ltac straightline_set' :=
      idtac;
      lazymatch goal with
      | [ |- @cmd _ _ _ _ _ _ _ (Syntax.cmd.set ?s ?e) _ _ _ ?post ]
        => time "handle set"
                (unfold1_cmd_goal; (cbv beta match delta [cmd_body]);
                 (let x := ident_of_string.ident_of_string s in
                  let x' := fresh x in
                  try (rename x into x');
                  time "letexists" letexists _ as x;
                  time "split" split))
      end.
    Ltac straightline_unfold_expr :=
      lazymatch goal with
      | |- @dexpr _ _ _ _ _ _ _ _ => idtac
      | |- @expr _ _ _ _ _ _ _ _ => idtac
      end;
      time "unfold" repeat
           match goal with
           | |- @dexpr _ _ _ _ _ _ _ _ => cbv beta delta [dexpr]
           | |- @expr _ _ _ _ _ _ _ _ => unfold1_expr_goal; (cbv beta match delta [expr_body])
           | |- @get _ _ _ _ _ _ => (cbv beta delta [get])
           | |- @literal _ _ _ _ => (cbv beta delta [literal])
           end.
    Ltac straightline_eexists_intro_split :=
      lazymatch goal with
      | [ |- @ex _ (fun x => and ?P ?Q) ]
        => let x' := fresh x in
           time "refine let_ex_intro_split" refine (let x' := _ in @ex_intro _ (fun x => and P Q) x' (@conj (match x' with x => P end) (match x' with x => Q end) _ _))
      end.
    Ltac intro_let :=
      idtac;
      lazymatch goal with
      | [ |- dlet x := ?v in ?P ]
        => time "intro let" (change (let x := v in P); intros)
      end.
    Ltac print_context_size' base :=
      lazymatch goal with
      | [ H : _ |- _ ] => revert H; print_context_size' (S base)
      | _ => idtac "Context size:" base
      end.
    Ltac print_context_size := assert_succeeds (idtac; print_context_size' O).
    Ltac do_refl_slow :=
      lazymatch goal with
      | |- @eq ?T1 (@map.get string (@word.rep _ _) _ _ _) (@Some ?T ?v) =>
          time "refl"
               (idtac;
                let v' := rdelta.rdelta v in
                is_evar v'; change v with v'; exact (@eq_refl T1 (@Some T v')))
      | |- @eq ?T ?x ?y
        => time "refl"
                (idtac;
                 let x := rdelta.rdelta x in
                 is_evar x; change (@eq T x y);
                 exact (@eq_refl T y))
      end.
    Ltac do_refl :=
      lazymatch goal with
      | |- @eq ?T1 (@map.get string (@word.rep _ _) _ _ _) (@Some ?T ?v) =>
          time "refl"
               (idtac;
                let v' := rdelta.rdelta v in
                is_evar v'; change v with v'; exact (@eq_refl T1 (@Some T v')))
      | |- @eq ?T ?x ?y
        => time "refl"
                (idtac;
                 let x := rdelta.rdelta x in
                 is_evar x; change (@eq T x y);
                 exact (@eq_refl T y))
      end.
    Ltac prof_refl :=
      print_context_size; match goal with
      | |- @eq ?T1 (@map.get string (@word.rep _ _) _ _ _) (@Some ?T ?v) =>
          let v' := rdelta.rdelta v in
          is_evar v'; change v with v'; do 100 assert_succeeds (once time "slow" exact (@eq_refl _ _)); do 100 assert_succeeds (once time "fast" exact (@eq_refl T1 (@Some T v'))); exact (@eq_refl T1 (@Some T v')) end.
    Ltac step :=
      repeat lazymatch goal with
             | [ |- cmd _ ?c _ _ _ _ ]
               => is_var c;
                  straightline_subst
             end; [];
      straightline_set';
      [ straightline_unfold_expr; [];
        straightline_eexists_intro_split;
        [ do_refl
        | straightline_unfold_expr;
          repeat intro_let;
          try do_refl ]
      | intro_let ].
    Ltac straightline_cleanup_clear ::= fail.
    Ltac cbn_interp_binop ::= fail.
    Ltac straightline_cleanup_subst ::= fail.
    (*Ltac straightline_set ::= match goal with |- WeakestPrecondition.cmd _ (Syntax.cmd.set ?s ?e) _ _ _ ?post => shelve end.*)
    (*Ltac straightline_split ::=
      match goal with
      | |- exists l', Interface.map.of_list_zip ?ks ?vs = Some l' /\ _ => idtac
      | |- exists l', Interface.map.putmany_of_list_zip ?ks ?vs ?l = Some l' /\ _ => idtac
      | |- exists x, ?P /\ ?Q => idtac
      | |- exists x, Markers.split (?P /\ ?Q) => idtac
      | |- Markers.unique (exists x, Markers.split (?P /\ ?Q)) => idtac
      | |- Markers.unique (Markers.left ?G) => idtac
      | |- Markers.split ?G => idtac
      end;
      shelve.*)
    Ltac straightline_side_condition_solver ::= idtac.
    Ltac straightline_side_condition_solver_inline ::= solve [ repeat straightline ].
    (* Ltac straightline_refl :=
  first
  [ match goal with
    | |- @eq (@map.rep string (@word.rep _ _) _) _ _ => idtac
    end; eapply (@SortedList.eq_value _ _ _); refine (@eq_refl _ _)
  | match goal with
    | |- @eq _ (@map.get string (@word.rep _ _) ?M ?m ?k) (@Some _ ?e') =>
          let e := rdelta.rdelta e' in
          is_evar e;
           once
            (let v :=
              multimatch goal with
              | x:=context [ @map.put _ _ M _ k ?v ]:_ |- _ => v
              end
             in
             unify e v; refine (@eq_refl _ (@Some _ v)))
    end
  | let v :=
     match goal with
     | |- @eq _ (@map.get string (@word.rep _ _) _ _ _) (@Some _ ?v) => v
     end
    in
    let v' := rdelta.rdelta v in
    is_evar v'; change v with v'; refine (@eq_refl _ _)
  | let x := match goal with
             | |- @eq _ ?x ?y => x
             end in
    let y := match goal with
             | |- @eq _ ?x ?y => y
             end in
    first
    [ let y := rdelta.rdelta y in
      is_evar y; change (@eq _ x y); refine (@eq_refl _ _)
    | let x := rdelta.rdelta x in
      is_evar x; change (@eq _ x y); refine (@eq_refl _ _)
    | let x := rdelta.rdelta x in
      let y := rdelta.rdelta y in
      constr_eq x y; refine (@eq_refl _ _) ] ]
     *)
    Ltac straightline_refl ::= first
  [ match goal with
    | |- @eq (@map.rep string (@word.rep _ _) _) _ _ => idtac
    end; eapply (@SortedList.eq_value _ _ _); assert_succeeds refine (@eq_refl _ _); shelve
  | match goal with
    | |- @eq _ (@map.get string (@word.rep _ _) ?M ?m ?k) (@Some _ ?e') =>
          let e := rdelta.rdelta e' in
          is_evar e;
           once
            (let v :=
              multimatch goal with
              | x:=context [ @map.put _ _ M _ k ?v ] |- _ => v
              end
             in
             unify e v; assert_succeeds refine (@eq_refl _ (@Some _ v))); shelve
    end
  | let v :=
     match goal with
     | |- @eq _ (@map.get string (@word.rep _ _) _ _ _) (@Some _ ?v) => v
     end
    in
    let v' := rdelta.rdelta v in
    is_evar v'; change v with v'; assert_succeeds refine (@eq_refl _ _); shelve
  | let x := match goal with
             | |- @eq _ ?x ?y => x
             end in
    let y := match goal with
             | |- @eq _ ?x ?y => y
             end in
    first
    [ let y := rdelta.rdelta y in
      is_evar y; change (@eq _ x y); assert_succeeds refine (@eq_refl _ _); shelve
    | let x := rdelta.rdelta x in
      is_evar x; change (@eq _ x y); assert_succeeds refine (@eq_refl _ _); shelve
    | let x := rdelta.rdelta x in
      let y := rdelta.rdelta y in
      constr_eq x y; assert_succeeds refine (@eq_refl _ _); shelve ] ].
    Set Ltac Profiling. Reset Ltac Profile.
    Set Printing Coercions.
    Set Printing Depth 1000000000.
    Set Printing Implicit.
    repeat match goal with H : _ |- _ => revert H end.
    Time unshelve (do 100 straightline); shelve_unifiable.
    Reset Ltac Profile.
    Optimize Proof.
    all: cbn [interp_binop].
    Time all: match goal with
              | [ |- ?ev = ?v :> ?T ]
                => is_evar ev; instantiate(1:=v); reflexivity
              | _ => idtac
    end.
    42: { match goal with
                | [ |- ?x = @Some ?T ?ev ]
                  => is_evar ev;
                     transitivity (@Some T (match x return match x with Some _ => T | None => unit end with
                                            | Some v => v
                                            | None => tt
                                            end <: T))
      end.
          (* Error: Conversion test raised an anomaly:
Anomaly "File "kernel/vconv.ml", line 199, characters 18-24: Assertion failed."
Please report at http://coq.inria.fr/bugs/.
 *)
              | _ => idtac
                end .. | ].
    1-41: give_up.
    2-15: give_up.
    Unshelve.
    all: shelve_unifiable.
    2: {
    1: revert x2 v0.
    2-30:match goal with
              | [ |- ?ev = ?v :> ?T ]
                => is_evar ev; instantiate(1:=v); reflexivity
              | _ => idtac
         end.
    {

    2: reflexivity.
    2: reflexivity.
    42: {
    all: try let v :=
     match goal with
     | |- @eq _ (@map.get string (@word.rep _ _) _ _ _) (@Some _ ?v) => v
     end
    in
    let v' := rdelta.rdelta v in
    is_evar v'; change v with v'.
    Time all: [ > match goal with
                | [ |- ?x = @Some ?T ?ev ]
                  => is_evar ev;
                first [ instantiate (1:=match x return match x with Some _ => T | None => unit end with
                                | Some v => v
                                | None => tt
                                        end <: T)
                      | transitivity (@Some T (match x return match x with Some _ => T | None => unit end with
                                | Some v => v
                                | None => tt
                                               end <: T))
                                     ]
              | _ => idtac
                end .. | ].
    42: { instantiate(1:=ltac:(clear -l23)).
          revert v0.
          clear -i.
          move i at bottom.
      lazymatch goal with
                | [ |- ?x = @Some ?T ?ev ]
                  => is_evar ev;
                     transitivity (@Some T (match x return match x with Some _ => T | None => unit end with
                                            | Some v => v
                                            | None => tt
                                            end <: T))
      end.
      lazymatch goal with
                | [ |- ?x = @Some ?T ?ev ]
                  => is_evar ev;
                instantiate (1:=ltac:(refine (match x return match x with Some _ => T | None => unit end with
                                | Some v => v
                                | None => tt
                                end <: T)))
      end.
              | _ => idtac
                end
    Time all: [ > cbv [reconstruct map.putmany_of_tuple List.length HList.tuple.of_list] in *.. | ].
    Time 1:match goal with
      | [ |- ?x = @Some ?T ?ev ]
        => instantiate (1:=match x return match x with Some _ => T | None => unit end with
                           | Some v => v
                           | None => tt
                           end <: T)
           end.
      Time reflexivity.
    Arguments map.get / . Arguments locals / .
    Time all: [ > cbn .. | ].
         cbn.
    Time all: [ > repeat match goal with H : Syntax.cmd.cmd |- _ => clear H end
                         .. | ].
    Time all: [ > repeat match goal with H := ?x : word.rep |- _ => tryif is_var x then subst H else clearbody H end
                         .. | ].
    Time all: [ > try (cbv; reflexivity) .. | ].

    1: vm_compute.
    Time all: [ > reflexivity .. | ].
    Time all: [ > match goal with
         | |- context G [@map.get ?K ?V ?M ?m ?k] =>
             time "all" (idtac; let v := match goal with H := context [map.put _ k ?v] |- _ => v end in
                                try cbv -[v]) end .. | ].
                                let goal := context G [Some v] in
                                time "change" change goal)
         end .. | ].
    all: shelve_unifiable.
    1: reflexivity.
    all: try let v :=
     match goal with
     | |- @eq _ (@map.get string (@word.rep _ _) _ _ _) (@Some _ ?v) => v
     end
    in
    let v' := rdelta.rdelta v in
    is_evar v'; change v with v'.
    Time all: [ > lazymatch goal with
                  | [ |- map.get ?v _ = _ ]
                    => instantiate (1:=ltac:(clear -v)); clear -v
              | [ |- ?ev = interp_binop _ ?v1 ?v2 ]
                => instantiate (1:=ltac:(clear -v1 v2)); clear -v1 v2
                end .. | ].
    all: cbn [interp_binop].
    Time all: match goal with
              | [ |- ?ev = ?v :> ?T ]
                => is_evar ev; refine (@eq_refl T v)
              | _ => idtac
    end.
    Time all: shelve_unifiable.

    Time all: [ > do 5 assert_succeeds reflexivity .. | ].
    Time 1: lazymatch goal with |- @eq ?T ?x ?y => refine (@eq_refl T y) end.
    Optimize Proof.
    Time 1: refine eq_refl.
    Optimize Proof.
    Time 1: reflexivity.
    Optimize Proof.
    Time all: [ > do 5 assert_succeeds reflexivity .. | ]. (* Finished transaction in 28.705 secs (27.704u,1.s) (successful) *)
    Time all: [ > do 5 assert_succeeds refine eq_refl .. | ]. (* Finished transaction in 36.655 secs (36.584u,0.069s) (successful) *)
   Time instantiate (1:=ltac:(clear -localsmap)).
      Time clear -localsmap.
      Time reflexivity.
    Time all: cbn [interp_binop].
    Time all: [ > lazymatch goal with |- @eq ?T ?x ?y => do 5 assert_succeeds refine (@eq_refl T y) end .. | ]. (* Finished transaction in 21.849 secs (21.839u,0.009s) (successful) *)
    Time all: [ > lazymatch goal with |- @eq ?T ?x ?y => do 5 assert_succeeds refine (@eq_refl T x) end .. | ]. (* Finished transaction in 37.437 secs (37.376u,0.06s) (successful) *)
    Time all: [ > lazymatch goal with
                  | [ |- @eq ?T ?x (@Some ?U ?y) ]
                    => time "a" refine (@eq_refl T (@Some U y))
                  | [ |- @eq ?T ?ev ?y ]
                    => is_evar ev; time "b" refine (@eq_refl T y)
                  | _ => idtac
                  end .. | ].
    Time 1: reflexivity.
    Time all: [ > refine eq_refl
                         .. | ].
    Show Ltac Profile.
    HERE
    (*Time unshelve (do 100 straightline); shelve_unifiable.*)
    Optimize Proof.

    repeat match goal with
           | [ H : Syntax.cmd.cmd |- _ ] => subst H
           end.
    Optimize Proof.
    Time idtac;  let s := match goal with |- WeakestPrecondition.cmd _ (Syntax.cmd.set ?s ?e) _ _ _ ?post => s end in
           unfold1_cmd_goal; (cbv beta match delta [cmd_body]);
                               let x := ident_of_string.ident_of_string s in
                               ensure_free x;
    lazymatch goal with
    | [ |- ex ?T ]
      => lazymatch T with
         | (fun y : ?A => and ?P ?Q)
           => notypeclasses refine (let x : A := _ in let P' : Prop := match x return Prop with y => P end in let Q' : Prop := match x return Prop with y => Q end in @ex_intro A (fun y : A => and P' Q') x (@conj P' Q' _ _))
         end
    end.
    letexists _ as x; split.
    (* NOTE: keep this consistent with the [exists _, _ /\ _] case far below *)
    letexists _ as x; split; [solve [repeat straightline]|].
    Show Ltac Profile.
    HERE
    Time repeat straightline_subst.
    HERE
    Time repeat straightline.
    Time unshelve (repeat (repeat straightline_subst; straightline_set'; [ shelve | intro_let ])); shelve_unifiable; [ .. | shelve ].
    Time all: straightline_unfold_expr.
    Time all: straightline_eexists_intro_split.
    Time all: try straightline_unfold_expr.
    Time all: try straightline_eexists_intro_split.
    Time all: try intro_let.
    Time all: do_refl.
    Unshelve.
    lazymatch goal with |- cmd _ _ _ _ _ ?postc => set (post := postc) end.
    repeat match goal with H : Syntax.cmd.cmd |- _ => subst H end.
    Time straightline_subst; straightline_set'; [ shelve | intro_let ].
    Time unshelve (repeat (repeat straightline_subst; straightline_set; [ shelve | intro_let ])); shelve_unifiable; [ .. | shelve ].
    Time all: straightline_unfold_expr.
    Time all: straightline_eexists_intro_split.
    Time all: try straightline_unfold_expr.
    Time all: try straightline_eexists_intro_split.
    Time all: try intro_let.
    Time all: do_refl.
    Unshelve.
    all: shelve_unifiable.
    1: straightline_unfold_expr; straightline_eexists_intro_split.
    1: do_refl.
    1: straightline_unfold_expr; intro_let.
    1: do_refl.
    subst post.

    cbv beta.
    (* prove [enforce] *)
    match goal with |- Markers.unique (Markers.left (exists x131 x132 x133 x134 x135 x136 x137 x138 x139 x140 x141 x142 x143 x144 x145 x146 x147 x148 x149 x150 x151, _)) => idtac end.

    repeat letexists. split.
    {
      cbv [enforce gather].
      Time repeat match goal with
                  | [ H : ?T |- _ ]
                    => lazymatch T with
                       | word.rep
                         => (let v := (eval cbv delta [H] in H) in
                             (tryif is_evar v then fail else clearbody H))
                       end
                  end.
      Time cbv.
      split; reflexivity. }

                             (*try revert H)
                       | _ => first [ clear H | revert H ]
                       end
                  end.

      Time intros.
      let e := open_constr:(_) in
      cut e.
      { Time repeat match goal with
                    | [ H : ?T |- _ ]
                      => lazymatch T with
                         | word.rep => clearbody H
                         end
                    end.
        intro H'.
        Time vm_compute.

      | _ => first [ clear H | revert H ]
        end
        end.
        Time intros.

        Time repeat match goal with H : word.rep |- _ => clearbody H end.
        repeat match goal with H : _ |- _ => clear H end.
        Time vm_compute.
        exact H'. }

      split; reflexivity.
      repeat match goal with
      | |- context G [@map.get ?K ?V ?M ?m ?k] =>
        time "all" (idtac; let v := match goal with H := context [map.put _ k ?v] |- _ => v end in
        let goal := context G [Some v] in
        time "change" change goal)
      end.
    cbv beta iota.
    split; refine eq_refl.
    }



    Time all: try do_refl.
    Unshelve.
    allg

    Time repeat straightline_subst; straightline_set; [ shelve | intro_let ].
    Time repeat straightline_subst; straightline_set; [ shelve | intro_let ].
    Time repeat straightline_subst; straightline_set; [ shelve | intro_let ].
    1:straightline_unfold_expr.
    1: straightline_eexists_intro_split.
    1: do_refl.
    1: straightline_unfold_expr.
    1: repeat intro_let.
    1: do_refl.₂
    repeat lazymatch goal with
             | [ |- cmd _ ?c _ _ _ _ ]
               => is_var c;
                  straightline_subst
             end; [].

    straightline_set; [ | intro_let ].
    step.
    1: straightline_eexists_intro_split.
    straightline_subst; [].
      straightline_set;
      [ | intro_let ].
    step.
    straightline_set.
    1: straightline_unfold_expr.
    1: straightline_eexists_intro_split.
    1: do_refl.
    1: straightline_unfold_expr.
    1: intro_let.
    1: do_refl.
    1: intro_let.

    1: intro_let.
      end.

    Set Ltac Profiling. Reset Ltac Profile.
    Time straightline_set. Show Ltac Profile.
    { match goal with
    | |- @dexpr _ _ _ _ _ _ _ _ => idtac
      end; cbv beta delta [dexpr].
      match goal with
      | |- @expr _ _ _ _ _ _ _ _ => idtac
      end; unfold1_expr_goal; (cbv beta match delta [expr_body]).
      match goal with
      | |- @expr _ _ _ _ _ _ _ _ => idtac
      end; unfold1_expr_goal; (cbv beta match delta [expr_body]).
      match goal with
      | |- @get _ _ _ _ _ _ => idtac
      end; (cbv beta delta [get]).
      (*repeat match goal with H : _ |- _ => clear H end.*)
      Time match goal with
           | |- @ex _ (fun x => and ?P ?Q) =>
               let x := fresh x in
               refine (let x := _ in @ex_intro _ (fun x => and P Q) x _); split
      end.
      Ltac print_context_size' base :=
        lazymatch goal with
        | [ H : _ |- _ ] => revert H; print_context_size' (S base)
        | _ => idtac "Context size:" base
        end.
      Ltac print_context_size := assert_succeeds (idtac; print_context_size' O).
      1: print_context_size; match goal with
      | |- @eq ?T1 (@map.get string (@word.rep _ _) _ _ _) (@Some ?T ?v) =>
          let v' := rdelta.rdelta v in
          is_evar v'; change v with v'; do 100 assert_succeeds (once time "slow" exact (@eq_refl _ _)); do 100 assert_succeeds (once time "fast" exact (@eq_refl T1 (@Some T v'))); exact (@eq_refl T1 (@Some T v')) end.
      match goal with
      | |- @expr _ _ _ _ _ _ _ _ => idtac
      end; unfold1_expr_goal; (cbv beta match delta [expr_body]).
      match goal with
      | |- @literal _ _ _ _ => idtac
      end; cbv beta delta [literal].
      Time match goal with
           | |- dlet x := ?v in
               ?P => change (let x := v in P)
           end; intros.
    match goal with
    | |- @eq ?T ?x ?y
      => let x := rdelta.rdelta x in
         is_evar x; change (@eq T x y);
         time exact (@eq_refl T y)
    end. }
    Time match goal with
           | |- dlet x := ?v in
               ?P => change (let x := v in P)
         end; intros.


    first
    [ (*let y := rdelta.rdelta y in
      is_evar y; change (@eq _ x y); exact (@eq_refl _ _)
    | *)let x := rdelta.rdelta x in
      is_evar x; change (@eq _ x y); exact (@eq_refl _ _) ].
    | let x := rdelta.rdelta x in
      let y := rdelta.rdelta y in
      constr_eq x y; exact (@eq_refl _ _) ].
      Print Ltac straightline_cleanup.
      Time match goal with
    | |- @dlet.dlet _ _ ?v (fun x => ?P) => change (let x := v in P)
    end; intros.
      repeat (straightline; match goal with |- dlet v := _ in _ => idtac end).
      Set Printing All.
      Print Ltac straightline_cleanup.
      Info 1 straightline.
      Info 1 straightline.
      Info 1 straightline.
          [ solve [ repeat straightline ] |  ]

    Time 1: solve [ repeat straightline ].
    all: [ >

    repeat match goal with
           | [ H : Syntax.cmd.cm

  |
  | let c := match goal with
             | |- @cmd _ _ _ _ _ _ _ ?c _ _ _ ?post => c
             end in
    let post := match goal with
                | |- @cmd _ _ _ _ _ _ _ ?c _ _ _ ?post => post
                end in
    let c := eval hnf in c in
    lazymatch c with
    | Syntax.cmd.while _ _ => fail
    | Syntax.cmd.cond _ _ _ => fail
    | Syntax.cmd.interact _ _ _ => fail
    | _ => idtac
    end; unfold1_cmd_goal; cbv beta match delta [cmd_body]
  | match goal with
    | |- @list_map _ _ (@get _ _ _ _) _ _ => idtac
    end; unfold1_list_map_goal; cbv beta match delta [list_map_body]
  | match goal with
    | |- @list_map _ _ (@expr _ _ _ _ _ _) _ _ => idtac
    end; unfold1_list_map_goal; cbv beta match delta [list_map_body]
  | match goal with
    | |- @list_map _ _ _ (@nil _) _ => idtac
    end; cbv beta match fix delta [list_map list_map_body]
  | match goal with
    | |- @expr _ _ _ _ _ _ _ _ => idtac
    end; unfold1_expr_goal; cbv beta match delta [expr_body]
  | match goal with
    | |- @dexpr _ _ _ _ _ _ _ _ => idtac
    end; cbv beta delta [dexpr]
  | match goal with
    | |- @dexprs _ _ _ _ _ _ _ _ => idtac
    end; cbv beta delta [dexprs]
  | match goal with
    | |- @literal _ _ _ _ => idtac
    end; cbv beta delta [literal]
  | match goal with
    | |- @get _ _ _ _ _ _ => idtac
    end; cbv beta delta [get]
  | match goal with
    | |- @load _ _ _ _ _ _ _ => idtac
    end; cbv beta delta [load]
  | match goal with
    | |- @enforce ?width ?word ?locals ?names ?values ?map =>
          let values := eval compute in values in
          change (@enforce width word locals names values map); exact
           (@conj _ _ (@eq_refl _ values) (@eq_refl _ _))
    end
  | match goal with
    | |- @eq (@map.rep string (@word.rep _ _) _) _ _ => idtac
    end; eapply (@SortedList.eq_value _ _ _); exact (@eq_refl _ _)
  | match goal with
    | |- @eq _ (@map.get string (@word.rep _ _) ?M ?m ?k) (@Some _ ?e') =>
          let e := rdelta.rdelta e' in
          is_evar e;
           once
            (let v :=
              multimatch goal with
              | x:=context [ @map.put _ _ M _ k ?v ]:_ (* XXX TODO Report Print Ltac bug *) |- _ => v
              end
             in
             unify e v; exact (@eq_refl _ (@Some _ v)))
    end
  | let v :=
     match goal with
     | |- @eq _ (@map.get string (@word.rep _ _) _ _ _) (@Some _ ?v) => v
     end
    in
    let v' := rdelta.rdelta v in
    is_evar v'; change v with v'; exact (@eq_refl _ _)
  | let x := match goal with
             | |- @eq _ ?x ?y => x
             end in
    let y := match goal with
             | |- @eq _ ?x ?y => y
             end in
    first
    [ let y := rdelta.rdelta y in
      is_evar y; change (@eq _ x y); exact (@eq_refl _ _)
    | let x := rdelta.rdelta x in
      is_evar x; change (@eq _ x y); exact (@eq_refl _ _)
    | let x := rdelta.rdelta x in
      let y := rdelta.rdelta y in
      constr_eq x y; exact (@eq_refl _ _) ]
  | match goal with
    | |- @store _ _ _ Syntax.access_size.one _ _ _ _ => idtac
    end; eapply (@store_one_of_sep _ _ _ _ _); [ solve [ ecancel_assumption ] |  ]
  | match goal with
    | |- @store _ _ _ Syntax.access_size.two _ _ _ _ => idtac
    end; eapply (@store_two_of_sep _ _ _ _ _); [ solve [ ecancel_assumption ] |  ]
  | match goal with
    | |- @store _ _ _ Syntax.access_size.four _ _ _ _ => idtac
    end; eapply (@store_four_of_sep _ _ _ _ _); [ solve [ ecancel_assumption ] |  ]
  | match goal with
    | |- @store _ _ _ Syntax.access_size.word _ _ _ _ => idtac
    end; eapply (@store_word_of_sep _ _ _ _ _); [ solve [ ecancel_assumption ] |  ]
  | let ev :=
     match goal with
     | |- @eq _ (@Memory.load _ _ _ Syntax.access_size.one ?m ?a) (@Some _ ?ev) =>
           ev
     end
    in
    try subst ev; refine (@load_one_of_sep _ _ _ _ _ _ _ _ _ _); ecancel_assumption
  | match goal with
    | |-
      @eq _ (@Memory.load _ ?word ?mem Syntax.access_size.two ?m ?a) (@Some _ ?ev)
      =>
          try subst ev; refine (@load_two_of_sep _ word _ mem _ a _ _ m _);
           ecancel_assumption
    end
  | match goal with
    | |-
      @eq _ (@Memory.load _ ?word ?mem Syntax.access_size.four ?m ?a) (@Some _ ?ev)
      =>
          try subst ev; refine
           (@load_four_of_sep_32bit _ word _ mem _ (@eq_refl _ _) a _ _ m _);
           ecancel_assumption
    end
  | match goal with
    | |-
      @eq _ (@Memory.load _ ?word ?mem Syntax.access_size.four ?m ?a) (@Some _ ?ev)
      =>
          try subst ev; refine (@load_four_of_sep _ word _ mem _ a _ _ m _);
           ecancel_assumption
    end
  | match goal with
    | |-
      @eq _ (@Memory.load _ ?word ?mem Syntax.access_size.word ?m ?a) (@Some _ ?ev)
      =>
          try subst ev; refine (@load_word_of_sep _ word _ mem _ a _ _ m _);
           ecancel_assumption
    end
  | match goal with
    | |-
      @ex _ (fun l' => and (@eq _ (@map.of_list_zip _ _ _ ?ks ?vs) (@Some _ l')) _)
      => idtac
    end; letexists; split; [ exact (@eq_refl _ _) |  ]
  | match goal with
    | |-
      @ex _
        (fun l' =>
         and (@eq _ (@map.putmany_of_list_zip _ _ _ ?ks ?vs ?l) (@Some _ l')) _) =>
          idtac
    end; letexists; split; [ exact (@eq_refl _ _) |  ]
  | match goal with
    | |- @ex _ (fun x => and ?P ?Q) =>
          let x := fresh x in
          refine (let x := _ in @ex_intro _ (fun x => and P Q) x _); split;
           [ solve [ repeat straightline ] |  ]
    | |- @ex _ (fun x => @Markers.split _ (and ?P ?Q)) =>
          let x := fresh x in
          refine (let x := _ in @ex_intro _ (fun x => and P Q) x _); split;
           [ solve [ repeat straightline ] |  ]
    | |- @Markers.unique _ (@ex _ (fun x => @Markers.split _ (and ?P ?Q))) =>
          let x := fresh x in
          refine (let x := _ in @ex_intro _ (fun x => and P Q) x _); split;
           [ solve [ repeat straightline ] |  ]
    end
  | let G := match goal with
             | |- @Markers.unique _ (@Markers.left _ ?G) => G
             end in
    change G; unshelve
     (idtac;
       repeat
        match goal with
        | |- @Markers.split _ (and ?P (@Markers.right _ ?Q)) =>
              split; [ eabstract repeat straightline | change Q ]
        | |- @ex _ (fun _ => _) => letexists
        end); [  ]
  | let G := match goal with
             | |- @Markers.split _ ?G => G
             end in
    change G; split
  | match goal with
    | |- True => idtac
    end; exact I
  | match goal with
    | |- or False _ => idtac
    end; right
  | match goal with
    | |- or _ False => idtac
    end; left
  | let z :=
     match goal with
     | |- and (@eq _ (Z.modulo ?z (bytes_per_word _)) Z0) _ => z
     end
    in
    lazymatch isZcst z with
    | true => idtac
    end; split; [ exact (@eq_refl _ _) |  ]
  | straightline_stackalloc
  | straightline_stackdealloc ].

    Set Printing All.
    Print Ltac straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    repeat (straightline; []).
    straightline.
    do 5 straightline.
    straightline.
    straightline.
    do 100 straightline.
    2: solve [intuition].
    straightline.
    straightline.
    straightline.
    straightline.
    do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.

    (* prove [enforce] *)
    match goal with |- Markers.unique (Markers.left (exists x131 x132 x133 x134 x135 x136 x137 x138 x139 x140 x141 x142 x143 x144 x145 x146 x147 x148 x149 x150 x151, _)) => idtac end.

    repeat letexists. split.
    {
      cbv [enforce gather].
      repeat match goal with
      | |- context G [@map.get ?K ?V ?M ?m ?k] =>
        let v := match goal with H := context [map.put _ k ?v] |- _ => v end in
        let goal := context G [Some v] in
        change goal
      end.
    cbv beta iota.
    split; refine eq_refl.
    }

    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time straightline.
    Time straightline.
    Time straightline.

    letexists. split.
    2:split.
    1: split.
    2: split.

    all : repeat straightline.
    all : try typeclasses eauto with core.

    {
      lazymatch goal with
      | [ H : word.unsigned br <> 0 |- _ ] =>
        subst br;
          rewrite word.unsigned_ltu in H;
          lazymatch type of H with
          | word.unsigned (if ?x <? ?y then _ else _) <> _ =>
            destruct (Z.ltb_spec0 x y) as [Hv |];
              rewrite word.unsigned_of_Z in H;
              cbv in H;
              [| congruence]
          end
      end.
      subst x131.
      subst v'.
      match goal with
      | [ |- word.unsigned ?w = _ ] =>
        change w with (word.add x (word.of_Z 1))
      end.
      rewrite word.unsigned_add, word.unsigned_of_Z.
      match goal with
      | [ H : word.unsigned _ = 10 - _ |- _ ] =>
        rewrite H in *
      end.
      rewrite word.unsigned_of_Z in Hv.
      change (word.wrap 10) with 10 in Hv.
      instantiate (1 := Nat.pred v).
      rewrite Nat2Z.inj_pred; [| blia].
      change (word.wrap 1) with 1.
      cbv [word.wrap].
      rewrite Z.mod_small; [blia |].
      split; [blia |].
      match goal with
      | [ H : (_ <= _)%nat |- _ ] =>
        let H' := fresh "H" in
        pose proof (inj_le _ _ H) as H'; cbn in H'
      end.
      match goal with
      | [ |- _ < 2^?w ] =>
          let w' := eval cbv in w in
          change w with w'
      end.
      blia.
    }
    { subst v'. blia. }
    { subst v'.
      lazymatch goal with
      | [ H : word.unsigned br <> 0 |- _ ] =>
        subst br;
          rewrite word.unsigned_ltu in H;
          lazymatch type of H with
          | word.unsigned (if ?x <? ?y then _ else _) <> _ =>
            destruct (Z.ltb_spec0 x y) as [Hv |];
              rewrite word.unsigned_of_Z in H;
              cbv in H;
              [| congruence]
          end
      end.
      match goal with
      | [ H : word.unsigned _ = 10 - _ |- _ ] =>
        rewrite H in *
      end.
      rewrite word.unsigned_of_Z in Hv.
      change (word.wrap 10) with 10 in Hv.
      apply lt_pred_n_n.
      apply Nat2Z.inj_lt.
      blia.
    }
  }

  subst Hsep.
  repeat straightline.
  replace (scalar32 x47 r) with (scalar32 (word.add x47 (word.of_Z 0)) r) in H8.
  2: {
    f_equal.
    1: {
      intros.
      rewrite H9.
      reflexivity.
    }
    ring.
  }
  repeat straightline.
  intuition.
  destruct out; cbn in H0; [| blia].
  cbn [array] in H19.
  let x := open_constr:(@cons word32 _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ nil)))))))))))))))) in
  unify out' x.
  subst out'.
  cbn [array].
  repeat match goal with
  | [ |- context[@word.add _ ?w (word.add x47 ?x) ?y] ] =>
    replace (@word.add _ w (word.add x47 x) y) with (@word.add _ w x47 (word.add x y)) by ring
  end.
  repeat match goal with
  | [ |- context[@word.add _ ?w (word.add x16 ?x) ?y] ] =>
    replace (@word.add _ w (word.add x16 x) y) with (@word.add _ w x16 (word.add x y)) by ring
  end.
  repeat match goal with
  | [ |- context[@word.add _ ?w (word.add x17 ?x) ?y] ] =>
    replace (@word.add _ w (word.add x17 x) y) with (@word.add _ w x17 (word.add x y)) by ring
  end.
  repeat match goal with
         | [ |- context[@word.add _ ?w (word.of_Z ?x) (word.of_Z ?y)] ] =>
           let z := eval cbv in (x + y) in
               change (@word.add _ w (word.of_Z x) (word.of_Z y)) with (@word.of_Z _ w z)
         end.
  rewrite !word.of_Z_unsigned in H19.
  repeat match type of H19 with
         | context[scalar32 ?a _] =>
           subst a
         end.
  replace (word.add x47 (word.of_Z 0)) with x47 in H19 by ring.
  ecancel_assumption.
Defined.
