Require Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef Coq.ZArith.BinInt coqutil.Z.Lia.
Require Import coqutil.sanity coqutil.Tactics.forward coqutil.Word.Interface. Import word.
Require Import Kami.Lib.Word.
Require riscv.Utility.Utility.
Require coqutil.Word.Naive.
From coqutil Require Import destr div_mod_to_equations.
From Stdlib Require Import Zmod.

Local Open Scope bool_scope.
Local Open Scope Z_scope.

(* [Zmod.of_Z m z] is [Zmod.mk m (if small z m then z else 0) <proof>], and the
   proof field repeats the value expression.  So reducing through it with
   [simpl]/[cbn] duplicates subterms at every nesting level (exponential), which
   is fatal for the processor and end2end proofs: without these declarations the
   final [Qed] of [end2end/End2EndPipeline.v] overflows the stack.  coqutil's
   Word/Naive.v documents the same trap for its own wrappers.  [vm_compute] and
   an explicit [cbv [...]] delta list are unaffected; a bare [cbv] is not, and
   must be avoided on goals mentioning words.

   These three are deliberately GLOBAL rather than [#[export]]: a global
   [Arguments] applies on [Require], an exported one only along [Import]
   chains, and [end2end/End2EndLightbulb.v] reaches this file only through
   non-[Export] [Require Import] chains, so [#[export]] would silently drop
   the declarations there and bring back the stack overflow. *)
Arguments Zmod.unsigned : simpl never.
Arguments Zmod.signed : simpl never.
Arguments Zmod.of_Z : simpl never.

(** [Kami.Lib.Word.word n] is the standard library's [bits (Z.of_nat n)], and every
    Kami word operation is a [simpl never] wrapper specified through
    [Zmod.unsigned].  So this bridge only has to transport the Kami [unsigned_*]
    lemmas from [Zmod.unsigned] to Kami's [wordToN]/[wordToZ] spellings, which is
    what [Z_of_wordToN] below does; nothing here computes with words. *)

Section KamiWordFacts.

  Lemma Z_of_wordToN: forall sz (w: Word.word sz), Z.of_N (wordToN w) = Zmod.unsigned w.
  Proof.
    intros; cbv [wordToN]; pose proof (@unsigned_range _ w); apply Z2N.id; blia.
  Qed.

  (* [uwordToZ] is now [Zmod.unsigned], no longer [Z.of_N (wordToN _)] by
     conversion, so the two spellings need this bridge. *)
  Lemma uwordToZ_kunsigned: forall sz (w: Word.word sz),
      uwordToZ w = Z.of_N (wordToN w).
  Proof. intros; symmetry; apply Z_of_wordToN. Qed.

  Lemma unsigned_mod_id: forall sz (w: Word.word sz),
      Zmod.unsigned w mod 2 ^ Z.of_nat sz = Zmod.unsigned w.
  Proof. intros; apply Z.mod_small, (@unsigned_range _ w). Qed.

  Lemma unsigned_wnot_mod: forall sz (w: Word.word sz),
      Zmod.unsigned (wnot w) = Z.lnot (Zmod.unsigned w) mod 2 ^ Z.of_nat sz.
  Proof.
    intros; rewrite unsigned_wnot.
    pose proof (@unsigned_range _ w); pose proof (pow2_pos_Z sz).
    unfold Z.lnot.
    replace (Z.pred (- Zmod.unsigned w))
      with (2 ^ Z.of_nat sz - 1 - Zmod.unsigned w + (-1) * 2 ^ Z.of_nat sz) by blia.
    rewrite Z.mod_add by blia.
    rewrite Z.mod_small by blia; reflexivity.
  Qed.

  Lemma wrshifta_ZToWord: forall sz (w: Word.word sz) n,
      wrshifta w n = ZToWord sz (wordToZ w / 2 ^ Z.of_nat n).
  Proof. reflexivity. Qed.

  Lemma weqb_eqb: forall sz (x y: Word.word sz),
      weqb x y = Z.eqb (Zmod.unsigned x) (Zmod.unsigned y).
  Proof.
    intros; cbv [weqb].
    destruct (Zmod.eqb_spec x y) as [E|E];
      destruct (Z.eqb_spec (Zmod.unsigned x) (Zmod.unsigned y)) as [E2|E2];
      try reflexivity.
    - subst; congruence.
    - exfalso; apply E, Zmod.unsigned_inj, E2.
  Qed.

  Lemma wordToN_split2 a b w :
    wordToN (@split2 a b w) = BinNat.N.div (wordToN w) (NatLib.Npow2 a).
  Proof.
    apply Znat.N2Z.inj.
    rewrite Znat.N2Z.inj_div, !Z_of_wordToN, NatLib.Z_of_N_Npow2.
    apply unsigned_split2.
  Qed.

  Lemma wordToN_split1 a b w :
    wordToN (@split1 a b w) = BinNat.N.modulo (wordToN w) (NatLib.Npow2 a).
  Proof.
    apply Znat.N2Z.inj.
    rewrite Znat.N2Z.inj_mod, !Z_of_wordToN, NatLib.Z_of_N_Npow2.
    apply unsigned_split1.
  Qed.

  Lemma wnot_idempotent:
    forall {sz} (w: word sz),
      wnot (wnot w) = w.
  Proof.
    intros; apply unsigned_inj; rewrite !unsigned_wnot.
    pose proof (@unsigned_range _ w); blia.
  Qed.

  Lemma wordToN_eq_rect:
    forall sz (w: Word.word sz) nsz Hsz,
      wordToN (eq_rect _ Word.word w nsz Hsz) = wordToN w.
  Proof.
    intros; subst; simpl; reflexivity.
  Qed.

  Lemma Z_pow_add_lor:
    forall n m p: Z,
      0 <= n < 2 ^ p -> 0 <= m -> 0 <= p ->
      (n + 2 ^ p * m)%Z = Z.lor n (2 ^ p * m).
  Proof.
    intros.
    apply eq_sym, BitOps.or_to_plus.
    rewrite Z.mul_comm, <-Z.shiftl_mul_pow2 by assumption.
    replace n with (Z.land n (Z.ones p)).
    - bitblast.Z.bitblast.
      rewrite Z.testbit_neg_r with (n:= l) by blia.
      apply Bool.andb_false_r.
    - destruct (Z.eq_dec n 0); [subst; apply Z.land_0_l|].
      assert (0 < n) by blia.
      rewrite Z.land_ones_low; [reflexivity|blia|].
      apply Z.log2_lt_pow2; blia.
  Qed.

  Lemma Z_of_wordToN_combine_alt:
    forall sz1 (w1: Word.word sz1) sz2 (w2: Word.word sz2),
      Z.of_N (wordToN (Word.combine w1 w2)) =
      Z.lor (Z.of_N (wordToN w1)) (Z.shiftl (Z.of_N (wordToN w2)) (Z.of_N (BinNat.N.of_nat sz1))).
  Proof.
    intros.
    pose proof (@unsigned_range _ w1); pose proof (@unsigned_range _ w2).
    rewrite !Z_of_wordToN, unsigned_combine, Znat.nat_N_Z.
    rewrite Z.shiftl_mul_pow2 by blia.
    rewrite (Z.mul_comm (Zmod.unsigned w2)).
    apply Z_pow_add_lor; blia.
  Qed.

  Lemma ZToWord_zero:
    forall n, ZToWord n 0 = wzero n.
  Proof.
    intros; apply unsigned_inj.
    rewrite unsigned_ZToWord, unsigned_wzero.
    pose proof (pow2_pos_Z n); apply Z.mod_0_l; blia.
  Qed.

  Lemma split1_wplus_silent:
    forall sz1 sz2 (w1 w2: Word.word (sz1 + sz2)),
      split1 sz1 sz2 w2 = wzero _ ->
      split1 sz1 sz2 (w1 ^+ w2) = split1 sz1 sz2 w1.
  Proof.
    intros sz1 sz2 w1 w2 H.
    apply (f_equal (@Zmod.unsigned _)) in H.
    rewrite unsigned_split1, unsigned_wzero in H.
    apply unsigned_inj.
    rewrite !unsigned_split1, unsigned_wplus.
    rewrite Z.mod_mod_divide by (exists (2 ^ Z.of_nat sz2); rewrite pow2_add_Z; ring).
    rewrite Zplus_mod, H, Z.add_0_r, Zmod_mod; reflexivity.
  Qed.

  Lemma sumbool_rect_weq {T} a b n x y :
    sumbool_rect (fun _ => T) (fun _ => a) (fun _ => b) (@weq n x y) = if weqb x y then a else b.
  Proof.
    cbv [sumbool_rect].
    destruct (weq _ _), (weqb _ _) eqn:?;
                                   try match goal with H : _ |- _ => eapply weqb_true_iff in H end;
      trivial; congruence.
  Qed.

  Lemma sumbool_rect_bool_weq n x y :
    sumbool_rect (fun _ => bool) (fun _ => true) (fun _ => false) (@weq n x y) = weqb x y.
  Proof. rewrite sumbool_rect_weq; destruct (weqb x y); trivial. Qed.

  Lemma unsigned_eqb n x y : Z.eqb (Z.of_N (wordToN x)) (Z.of_N (wordToN y)) = @weqb n x y.
  Proof. rewrite !Z_of_wordToN; symmetry; apply weqb_eqb. Qed.

  Lemma unsigned_split1_mod:
    forall n m w,
      Z.of_N (wordToN (split1 n m w)) = Z.of_N (wordToN w) mod (2 ^ (Z.of_nat n)).
  Proof. intros; rewrite !Z_of_wordToN; apply unsigned_split1. Qed.

End KamiWordFacts.

Section WithWidth.
  Context {width : Z}.
  Context {width_nonneg : Z.lt 0 width}.
  Local Notation sz := (Z.to_nat width).

  Definition kword: Type := Kami.Lib.Word.word sz.
  Definition kunsigned(x: kword): Z := Zmod.unsigned x.
  Definition ksigned: kword -> Z := @wordToZ sz.
  Definition kofZ: Z -> kword := ZToWord sz.

  (* The bridge to Kami's legacy [wordToN]-spelled lemma family. *)
  Lemma kunsigned_wordToN: forall x: kword, kunsigned x = Z.of_N (wordToN x).
  Proof. intros; symmetry; apply Z_of_wordToN. Qed.

  (** The word instance is coqutil's [Naive.word], field for field: this record
      is [Naive.word width] with its [rep] spelled [Kami.Lib.Word.word (Z.to_nat
      width)] instead of [bits width].  The two are convertible whenever [width]
      is a numeral (every use is at 32 or 8), so [KamiWord.word 32 = Naive.word
      32] holds by [eq_refl], and every field agrees with what the Kami
      processor computes ([Zmod.udiv x 0 = 2^width-1], [Zmod.umod x 0 = x], and
      Naive masks shift amounts with [mod width] at power-of-two widths, which
      is RISC-V's convention; see kami-stage3-report.md for the field-by-field
      check).  Spelling [rep] the Kami way matters: Kami's API is indexed by a
      [nat] size, and unification cannot recover [?sz] from [bits width], so
      [wordToN a] for [a : word] would need an annotation at every use. *)
  Local Notation Nv := (Naive.word (Z.of_nat sz)).
  Definition word : word.word width := {|
    rep := kword;
    unsigned := @word.unsigned _ Nv;
    signed := @word.signed _ Nv;
    of_Z := @word.of_Z _ Nv;
    add := @word.add _ Nv;
    sub := @word.sub _ Nv;
    opp := @word.opp _ Nv;
    or := @word.or _ Nv;
    and := @word.and _ Nv;
    xor := @word.xor _ Nv;
    not := @word.not _ Nv;
    ndn := @word.ndn _ Nv;
    mul := @word.mul _ Nv;
    mulhss := @word.mulhss _ Nv;
    mulhsu := @word.mulhsu _ Nv;
    mulhuu := @word.mulhuu _ Nv;
    divu := @word.divu _ Nv;
    divs := @word.divs _ Nv;
    modu := @word.modu _ Nv;
    mods := @word.mods _ Nv;
    slu := @word.slu _ Nv;
    sru := @word.sru _ Nv;
    srs := @word.srs _ Nv;
    eqb := @word.eqb _ Nv;
    ltu := @word.ltu _ Nv;
    lts := @word.lts _ Nv;
    sextend := @word.sextend _ Nv;
  |}.

  (* [Naive.ok] transported along [Z.of_nat (Z.to_nat width) = width]; the
     abstraction is well typed because no field type of [word.word] mentions the
     width, only [rep]. *)
  Lemma ok : word.ok word.
  Proof using width_nonneg.
    assert (Hw: Z.of_nat sz = width) by (apply Znat.Z2Nat.id; blia).
    cbv [word kword Kami.Lib.Word.word].
    rewrite Hw.
    exact (Naive.ok width width_nonneg).
  Qed.
End WithWidth.
Arguments word : clear implicits.
Arguments ok : clear implicits.
Arguments kword : clear implicits.

#[global] Existing Instance word.
#[global] Existing Instance ok.

(* At the widths in use the two instances are the same term. *)
Lemma word32_Naive: word 32 = Naive.word 32. Proof. reflexivity. Qed.
Lemma word8_Naive: word 8 = Naive.word 8. Proof. reflexivity. Qed.

(* The instance's fields in Kami's spelling, all by conversion.  [rewrite] with
   these keeps goals in the vocabulary of Kami's lemma library without exposing
   the instance record (which a [cbv] through [KamiWord.word] would do). *)
Section Spelling.
  Context {width : Z}.
  Local Notation sz := (Z.to_nat width).
  Local Notation W := (word width).
  Lemma unsigned_eq (x: kword width): @word.unsigned width W x = Zmod.unsigned x. Proof. reflexivity. Qed.
  Lemma signed_eq (x: kword width): @word.signed width W x = wordToZ x. Proof. reflexivity. Qed.
  Lemma of_Z_eq (z: Z): @word.of_Z width W z = ZToWord sz z. Proof. reflexivity. Qed.
  Lemma add_eq (x y: kword width): @word.add width W x y = wplus x y. Proof. reflexivity. Qed.
  Lemma sub_eq (x y: kword width): @word.sub width W x y = wminus x y. Proof. reflexivity. Qed.
  Lemma mul_eq (x y: kword width): @word.mul width W x y = wmult x y. Proof. reflexivity. Qed.
  Lemma opp_eq (x: kword width): @word.opp width W x = wneg x. Proof. reflexivity. Qed.
  Lemma and_eq (x y: kword width): @word.and width W x y = wand x y. Proof. reflexivity. Qed.
  Lemma or_eq (x y: kword width): @word.or width W x y = wor x y. Proof. reflexivity. Qed.
  Lemma xor_eq (x y: kword width): @word.xor width W x y = wxor x y. Proof. reflexivity. Qed.
  Lemma not_eq (x: kword width): @word.not width W x = wnot x. Proof. reflexivity. Qed.
  Lemma eqb_eq (x y: kword width): @word.eqb width W x y = weqb x y. Proof. reflexivity. Qed.
  (* Naive's comparisons are [Z.ltb] on the representatives; Kami's are the
     decision procedures.  Equal, not convertible. *)
  Lemma ltu_eq (x y: kword width):
    @word.ltu width W x y = if wlt_dec x y then true else false.
  Proof.
    change (@word.ltu width W x y) with (Z.ltb (Zmod.unsigned x) (Zmod.unsigned y)).
    pose proof (@Z_of_wordToN _ x); pose proof (@Z_of_wordToN _ y).
    case (wlt_dec x y) as [Hlt|Hlt]; cbv [wlt] in Hlt;
      destruct (Z.ltb_spec (Zmod.unsigned x) (Zmod.unsigned y)); trivial; exfalso; blia.
  Qed.
  Lemma lts_eq (x y: kword width):
    @word.lts width W x y = if wslt_dec x y then true else false.
  Proof.
    change (@word.lts width W x y) with (Z.ltb (wordToZ x) (wordToZ y)).
    case (wslt_dec x y) as [Hlt|Hlt]; cbv [wslt] in Hlt;
      destruct (Z.ltb_spec (wordToZ x) (wordToZ y)); trivial; exfalso; blia.
  Qed.
End Spelling.


Open Scope Z_scope.

Section MkWords.
  Context {width : Z}.
  Context {width_cases : width = 32 \/ width = 64}.

  Lemma boundW: 0 < width.
  Proof.
    case width_cases; intro E; rewrite E; reflexivity.
  Defined.
  #[local] Instance wordW: word.word width := word width.
  #[local] Instance wordWok: word.ok wordW := ok width boundW.

  #[local] Instance word8: word.word 8 := word 8.
  #[local] Instance word8ok: word.ok word8 := ok 8 eq_refl.
End MkWords.
