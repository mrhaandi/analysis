(* -*- company-coq-local-symbols: (("`&`" . ?∩) ("`|`" . ?∪) ("set0" . ?∅)); -*- *)
(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import finmap fingroup perm rat.
Require Import boolp reals ereal classical_sets signed topology numfun.
Require Import mathcomp_extra functions normedtype.
From HB Require Import structures.
Require Import sequences esum measure fsbigop cardinality set_interval.
Require Import realfun.

(******************************************************************************)
(*                       Lebesgue Stieltjes Measure                           *)
(*                                                                            *)
(* This file contains a formalization of the Lebesgue-Stieltjes measure using *)
(* the Extension theorem available in measure.v.                              *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* TODO: move *)
Notation right_continuous f :=
  (forall x, f%function @ at_right x --> f%function x).

Lemma nondecreasing_right_continuousP (R : realType) (a : R) (e : R)
    (f : R -> R) (ndf : {homo f : x y / x <= y}) (rcf : (right_continuous f)) :
  e > 0 -> exists d : {posnum R}, f (a + d%:num) <= f a + e.
Proof.
move=> e0; move: rcf => /(_ a)/(@cvg_dist _ [normedModType R of R^o]).
move=> /(_ _ e0)[] _ /posnumP[d] => h.
exists (PosNum [gt0 of (d%:num / 2)]) => //=.
move: h => /(_ (a + d%:num / 2)) /=.
rewrite opprD addrA subrr distrC subr0 ger0_norm //.
rewrite ltr_pdivr_mulr// ltr_pmulr// ltr1n => /(_ erefl).
rewrite ltr_addl divr_gt0// => /(_ erefl).
rewrite ler0_norm; last by rewrite subr_le0 ndf// ler_addl.
by rewrite opprB ltr_subl_addl => fa; exact: ltW.
Qed.

(* TODO: move and use in lebesgue_measure.v? *)
Lemma le_inf (R : realType) (S1 S2 : set R) :
  -%R @` S2 `<=` down (-%R @` S1) -> nonempty S2 -> has_inf S1
    -> (inf S1 <= inf S2)%R.
Proof.
move=> S21 S12 S1i; rewrite ler_oppl opprK le_sup// ?has_inf_supN//.
exact/nonemptyN.
Qed.

Definition EFinf {R : numDomainType} (f : R -> R) : \bar R -> \bar R :=
  fun x => if x is r%:E then (f r)%:E else x.

Lemma nondecreasing_EFinf (R : realDomainType) (f : R -> R) :
  {homo f : x y / (x <= y)%R} -> {homo EFinf f : x y / (x <= y)%E}.
Proof.
move=> ndf.
by move=> [r| |] [l| |]//=; rewrite ?leey ?leNye// !lee_fin; exact: ndf.
Qed.

Section hlength.
Local Open Scope ereal_scope.
Variables (R : realType) (f : R -> R).
Hypothesis ndf : {homo f : x y / (x <= y)%R}.

Let g : \bar R -> \bar R := EFinf f.

Implicit Types i j : interval R.
Definition itvs : Type := R.

Definition hlength (A : set itvs) : \bar R := let i := Rhull A in g i.2 - g i.1.

Lemma hlength0 : hlength (set0 : set R) = 0.
Proof. by rewrite /hlength Rhull0 /= subee. Qed.

Lemma hlength_singleton (r : R) : hlength `[r, r] = 0.
Proof.
rewrite /hlength /= asboolT// sup_itvcc//= asboolT//.
by rewrite asboolT inf_itvcc//= ?subee// inE.
Qed.

Lemma hlength_itv i : hlength [set` i] = if i.2 > i.1 then g i.2 - g i.1 else 0.
Proof.
case: ltP => [/lt_ereal_bnd/neitvP i12|]; first by rewrite /hlength set_itvK.
rewrite le_eqVlt => /orP[|/lt_ereal_bnd i12]; last first.
  rewrite -hlength0; congr (hlength _).
  by apply/eqP/negPn; rewrite -/(neitv _) neitvE -leNgt (ltW i12).
case: i => -[ba a|[|]] [bb b|[|]] //=.
- rewrite /= => /eqP[->{b}]; move: ba bb => -[] []; try
    by rewrite set_itvE hlength0.
  by rewrite hlength_singleton.
- by move=> _; rewrite set_itvE hlength0.
- by move=> _; rewrite set_itvE hlength0.
Qed.

Lemma hlength_setT : hlength setT = +oo%E :> \bar R.
Proof. by rewrite /hlength RhullT. Qed.

Lemma hlength_finite_fin_num i : neitv i -> hlength [set` i] < +oo ->
  ((i.1 : \bar R) \is a fin_num) /\ ((i.2 : \bar R) \is a fin_num).
Proof.
move: i => [[ba a|[]] [bb b|[]]] /neitvP //=; do ?by rewrite ?set_itvE ?eqxx.
by move=> _; rewrite hlength_itv /= ltey.
by move=> _; rewrite hlength_itv /= ltNye.
by move=> _; rewrite hlength_itv.
Qed.

Lemma finite_hlengthE i : neitv i -> hlength [set` i] < +oo ->
  hlength [set` i] = (fine (g i.2))%:E - (fine (g i.1))%:E.
Proof.
move=> i0 ioo; have [i1f i2f] := hlength_finite_fin_num i0 ioo.
rewrite fineK; last first.
  by rewrite /g; move: i2f; case: (ereal_of_itv_bound i.2).
rewrite fineK; last first.
  by rewrite /g; move: i1f; case: (ereal_of_itv_bound i.1).
rewrite hlength_itv; case: ifPn => //; rewrite -leNgt le_eqVlt => /predU1P[->|].
  by rewrite subee// /g; move: i1f; case: (ereal_of_itv_bound i.1).
by move/lt_ereal_bnd/ltW; rewrite leNgt; move: i0 => /neitvP => ->.
Qed.

Lemma hlength_itv_bnd (a b : R) (x y : bool): (a <= b)%R ->
  hlength [set` Interval (BSide x a) (BSide y b)] = (f b - f a)%:E.
Proof.
move=> ab; rewrite hlength_itv/= lte_fin lt_neqAle ab andbT.
by have [-> /=|/= ab'] := eqVneq a b; rewrite ?subrr// EFinN EFinB.
Qed.

Lemma hlength_infty_bnd b r :
  hlength [set` Interval -oo%O (BSide b r)] = +oo :> \bar R.
Proof. by rewrite hlength_itv /= ltNye. Qed.

Lemma hlength_bnd_infty b r :
  hlength [set` Interval (BSide b r) +oo%O] = +oo :> \bar R.
Proof. by rewrite hlength_itv /= ltey. Qed.

Lemma pinfty_hlength i : hlength [set` i] = +oo ->
  (exists s r, i = Interval -oo%O (BSide s r) \/ i = Interval (BSide s r) +oo%O)
  \/ i = `]-oo, +oo[.
Proof.
rewrite hlength_itv; case: i => -[ba a|[]] [bb b|[]] //= => [|_|_|].
- by case: ifPn.
- by left; exists ba, a; right.
- by left; exists bb, b; left.
- by right.
Qed.

Lemma hlength_ge0 i : 0 <= hlength [set` i].
Proof.
rewrite hlength_itv; case: ifPn => //; case: (i.1 : \bar _) => [r| |].
- by rewrite suber_ge0// => /ltW /(nondecreasing_EFinf ndf).
- by rewrite ltNge leey.
- by case: (i.2 : \bar _) => //= [r _]; rewrite leey.
Qed.
Local Hint Extern 0 (0%:E <= hlength _) => solve[apply: hlength_ge0] : core.

Lemma hlength_Rhull (A : set R) : hlength [set` Rhull A] = hlength A.
Proof. by rewrite /hlength Rhull_involutive. Qed.

Lemma le_hlength_itv i j :
  {subset i <= j} -> hlength [set` i] <= hlength [set` j].
Proof.
set I := [set` i]; set J := [set` j].
have [->|/set0P I0] := eqVneq I set0; first by rewrite hlength0 hlength_ge0.
have [J0|/set0P J0] := eqVneq J set0.
  by move/subset_itvP; rewrite -/J J0 subset0 -/I => ->.
move=> /subset_itvP ij; apply: lee_sub => /=.
  have [ui|ui] := asboolP (has_ubound I).
    have [uj /=|uj] := asboolP (has_ubound J); last by rewrite leey.
    rewrite lee_fin; apply: ndf; apply/le_sup => //.
    by move=> r Ir; exists r; split => //; apply: ij.
  have [uj /=|//] := asboolP (has_ubound J).
  by move: ui; have := subset_has_ubound ij uj.
have [lj /=|lj] := asboolP (has_lbound J); last by rewrite leNye.
have [li /=|li] := asboolP (has_lbound I); last first.
  by move: li; have := subset_has_lbound ij lj.
rewrite lee_fin; apply/ndf/le_inf => //.
move=> r [r' Ir' <-{r}]; exists (- r')%R.
by split => //; exists r' => //; apply: ij.
Qed.

Lemma le_hlength : {homo hlength : A B / A `<=` B >-> A <= B}.
Proof.
move=> a b /le_Rhull /le_hlength_itv.
by rewrite (hlength_Rhull a) (hlength_Rhull b).
Qed.

End hlength.
Arguments hlength {R}.
#[global] Hint Extern 0 (0%:E <= hlength _) => solve[apply: hlength_ge0] : core.

Section itv_semiRingOfSets.
Variable R : realType.
Implicit Types (I J K : set R).
Definition ocitv_type : Type := R.

Definition ocitv := [set `]x.1, x.2]%classic | x in [set: R * R]].

Lemma is_ocitv a b : ocitv `]a, b]%classic.
Proof. by exists (a, b); split => //=; rewrite in_itv/= andbT. Qed.
Hint Extern 0 (ocitv _) => solve [apply: is_ocitv] : core.

Lemma ocitv0 : ocitv set0.
Proof. by exists (1, 0); rewrite //= set_itv_ge ?bnd_simp//= ltr10. Qed.
Hint Resolve ocitv0 : core.

Lemma ocitvP X : ocitv X <-> X = set0 \/ exists2 x, x.1 < x.2 & X = `]x.1, x.2]%classic.
Proof.
split=> [[x _ <-]|[->//|[x xlt ->]]]//.
case: (boolP (x.1 < x.2)) => x12; first by right; exists x.
by left; rewrite set_itv_ge.
Qed.

Lemma ocitvD : semi_setD_closed ocitv.
Proof.
move=> _ _ [a _ <-] /ocitvP[|[b ltb]] ->.
  rewrite setD0; exists [set `]a.1, a.2]%classic].
  by split=> [//|? ->//||? ? -> ->//]; rewrite bigcup_set1.
rewrite setDE setCitv/= setIUr -!set_itvI.
rewrite /Order.meet/= /Order.meet/= /Order.join/=
         ?(andbF, orbF)/= ?(meetEtotal, joinEtotal).
rewrite -negb_or le_total/=; set c := minr _ _; set d := maxr _ _.
have inside : a.1 < c -> d < a.2 -> `]a.1, c] `&` `]d, a.2] = set0.
  rewrite -subset0 lt_minr lt_maxl => /andP[a12 ab1] /andP[_ ba2] x /= [].
  have b1a2 : b.1 <= a.2 by rewrite ltW// (lt_trans ltb).
  have a1b2 : a.1 <= b.2 by rewrite ltW// (lt_trans _ ltb).
  rewrite /c /d (min_idPr _)// (max_idPr _)// !in_itv /=.
  move=> /andP[a1x xb1] /andP[b2x xa2].
  by have := lt_le_trans b2x xb1; case: ltgtP ltb.
exists ((if a.1 < c then [set `]a.1, c]%classic] else set0) `|`
        (if d < a.2 then [set `]d, a.2]%classic] else set0)); split.
- by rewrite finite_setU; do! case: ifP.
- by move=> ? []; case: ifP => ? // ->//=.
- by rewrite bigcup_setU; congr (_ `|` _);
     case: ifPn => ?; rewrite ?bigcup_set1 ?bigcup_set0// set_itv_ge.
- move=> I J/=; case: ifP => //= ac; case: ifP => //= da [] // -> []// ->.
    by rewrite inside// => -[].
  by rewrite setIC inside// => -[].
Qed.

Lemma ocitvI : setI_closed ocitv.
Proof.
move=> _ _ [a _ <-] [b _ <-]; rewrite -set_itvI/=.
rewrite /Order.meet/= /Order.meet /Order.join/=
        ?(andbF, orbF)/= ?(meetEtotal, joinEtotal).
by rewrite -negb_or le_total/=.
Qed.

Variable d : measure_display.

HB.instance Definition _ :=
  @isSemiRingOfSets.Build d ocitv_type (Pointed.class R) ocitv ocitv0 ocitvI ocitvD.

Definition itvs_semiRingOfSets := [the semiRingOfSetsType d of ocitv_type].

Variable f : R -> R.

Lemma hlength_semi_additive : semi_additive (hlength f : set ocitv_type -> _).
Proof.
move=> /= I n /(_ _)/cid2-/all_sig[b]/all_and2[_]/(_ _)/esym-/funext {I}->.
move=> Itriv [[/= a1 a2] _] /esym /[dup] + ->.
rewrite hlength_itv ?lte_fin/= -EFinB.
case: ifPn => a12; last first.
  pose I i :=  `](b i).1, (b i).2]%classic.
  rewrite set_itv_ge//= -(bigcup_mkord _ I) /I => /bigcup0P I0.
  by under eq_bigr => i _ do rewrite I0//= hlength0; rewrite big1.
set A := `]a1, a2]%classic.
rewrite -bigcup_pred; set P := xpredT; rewrite (eq_bigl P)//.
move: P => P; have [p] := ubnP #|P|; elim: p => // p IHp in P a2 a12 A *.
rewrite ltnS => cP /esym AE.
have : A a2 by rewrite /A /= in_itv/= lexx andbT.
rewrite AE/= => -[i /= Pi] a2bi.
case: (boolP ((b i).1 < (b i).2)) => bi; last by rewrite itv_ge in a2bi.
have {}a2bi : a2 = (b i).2.
  apply/eqP; rewrite eq_le (itvP a2bi)/=.
  suff: A (b i).2 by move=> /itvP->.
  by rewrite AE; exists i=> //=; rewrite in_itv/= lexx andbT.
rewrite {a2}a2bi in a12 A AE *.
rewrite (bigD1 i)//= hlength_itv ?lte_fin/= bi !EFinD -addeA.
congr (_ + _)%E; apply/eqP; rewrite addeC -sube_eq// 1?adde_defC//.
rewrite ?EFinN oppeK addeC; apply/eqP.
case: (eqVneq a1 (b i).1) => a1bi.
  rewrite {a1}a1bi in a12 A AE {IHp} *; rewrite subee ?big1// => j.
  move=> /andP[Pj Nji]; rewrite hlength_itv ?lte_fin/=; case: ifPn => bj//.
  exfalso; have /trivIsetP/(_ j i I I Nji) := Itriv.
  pose m := ((b j).1 + (b j).2) / 2%:R.
  have mbj : `](b j).1, (b j).2]%classic m.
     by rewrite /= !in_itv/= ?(midf_lt, midf_le)//= ltW.
  rewrite -subset0 => /(_ m); apply; split=> //.
  by suff: A m by []; rewrite AE; exists j => //.
have a1b2 j : P j -> (b j).1 < (b j).2 -> a1 <= (b j).2.
  move=> Pj bj; suff /itvP-> : A (b j).2 by [].
  by rewrite AE; exists j => //=; rewrite ?in_itv/= bj//=.
have a1b j : P j -> (b j).1 < (b j).2 -> a1 <= (b j).1.
  move=> Pj bj; case: ltP=> // bj1a.
  suff : A a1 by rewrite /A/= in_itv/= ltxx.
  by rewrite AE; exists j; rewrite //= in_itv/= bj1a//= a1b2.
have bbi2 j : P j -> (b j).1 < (b j).2 -> (b j).2 <= (b i).2.
  move=> Pj bj; suff /itvP-> : A (b j).2 by [].
  by rewrite AE; exists j => //=; rewrite ?in_itv/= bj//=.
apply/IHp.
- by rewrite lt_neqAle a1bi/= a1b.
- rewrite (leq_trans _ cP)// -(cardID (pred1 i) P).
  rewrite [X in (_ < X + _)%N](@eq_card _ _ (pred1 i)); last first.
    by move=> j; rewrite !inE andbC; case: eqVneq => // ->.
  rewrite ?card1 ?ltnS// subset_leq_card//.
  by apply/fintype.subsetP => j; rewrite -topredE/= !inE andbC.
apply/seteqP; split=> /= [x [j/= /andP[Pj Nji]]|x/= xabi].
  case: (boolP ((b j).1 < (b j).2)) => bj; last by rewrite itv_ge.
  apply: subitvP; rewrite subitvE ?bnd_simp a1b//= leNgt.
  have /trivIsetP/(_ j i I I Nji) := Itriv.
  rewrite -subset0 => /(_ (b j).2); apply: contra_notN => /= bi1j2.
  by rewrite !in_itv/= bj !lexx bi1j2 bbi2.
have: A x.
  rewrite /A/= in_itv/= (itvP xabi)/= ltW//.
  by rewrite (le_lt_trans _ bi) ?(itvP xabi).
rewrite AE => -[j /= Pj xbj].
exists j => //=.
apply/andP; split=> //; apply: contraTneq xbj => ->.
by rewrite in_itv/= le_gtF// (itvP xabi).
Qed.

Hint Extern 0 (measurable _) => solve [apply: is_ocitv] : core.

Lemma hlength_sigma_finite : sigma_finite [set: ocitv_type] (hlength f).
Proof.
exists (fun k : nat => `] (- k%:R)%R, k%:R]%classic).
  apply/esym; rewrite -subTset => /= x _ /=.
  exists `|(floor `|x|%R + 1)%R|%N; rewrite //= in_itv/=.
  rewrite !natr_absz intr_norm intrD -RfloorE.
  suff: `|x| < `|Rfloor `|x| + 1| by rewrite ltr_norml => /andP[-> /ltW->].
  rewrite [ltRHS]ger0_norm//.
    by rewrite (le_lt_trans _ (lt_succ_Rfloor _))// ?ler_norm.
  by rewrite addr_ge0// -Rfloor0 le_Rfloor.
by move=> k; split => //; rewrite hlength_itv /= -EFinB; case: ifP; rewrite ltey.
Qed.

Hypothesis ndf : {homo f : x y / (x <= y)%R}.

Lemma hlength_ge0' (I : set ocitv_type) : (0 <= hlength f I)%E.
Proof. by rewrite -(hlength0 f) le_hlength. Qed.

HB.instance Definition _ :=
  isAdditiveMeasure.Build _ R _ (hlength f : set ocitv_type -> _)
    hlength_ge0' hlength_semi_additive.

Lemma hlength_content_sub_fsum (D : {fset nat}) a0 b0
    (a b : nat -> R) : (forall i, i \in D -> a i <= b i) ->
    `]a0, b0] `<=` \big[setU/set0]_(i <- D) `] a i, b i]%classic ->
  f b0 - f a0 <= \sum_(i <- D) (f (b i) - f (a i)).
Proof.
move=> Dab h; have [ab|ab] := leP a0 b0; last first.
  apply (@le_trans _ _ 0); first by rewrite subr_le0 ndf// ltW.
  by rewrite big_seq sumr_ge0// => i iD; rewrite subr_ge0 ndf// Dab.
have mab k :
  [set` D] k -> @measurable d itvs_semiRingOfSets `]a k, b k]%classic by [].
move: h; rewrite -bigcup_fset.
move/(@content_sub_fsum d R _
    [the additive_measure _ _ of hlength f : set ocitv_type -> _] _ [set` D]
    `]a0, b0]%classic (fun x => `](a x), (b x)]%classic) (finite_fset D) mab
  (is_ocitv _ _)) => /=.
rewrite hlength_itv_bnd// -lee_fin => /le_trans; apply.
rewrite -sumEFin fsbig_finite//= set_fsetK// big_seq [in X in (_ <= X)%E]big_seq.
by apply: lee_sum => i iD; rewrite hlength_itv_bnd// Dab.
Qed.

Lemma hlength_sigma_sub_additive (rcf : right_continuous f) :
  sigma_sub_additive (hlength f : set ocitv_type -> _).
Proof.
move=> I A /(_ _)/cid2-/all_sig[b]/all_and2[_]/(_ _)/esym AE.
move=> [a _ <-]; rewrite hlength_itv ?lte_fin/= -EFinB => lebig.
case: ifPn => a12; last first.
  rewrite nneseries_esum; last by move=> ? _; exact: hlength_ge0'.
  by rewrite esum_ge0// => ? _; exact: hlength_ge0'.
wlog wlogh : b A AE lebig / forall n, (b n).1 <= (b n).2.
  move=> /= h.
  set A' := fun n => if (b n).1 >= (b n).2 then set0 else A n.
  set b' := fun n => if (b n).1 >= (b n).2 then (0, 0) else b n.
  rewrite [X in (_ <= X)%E](_ : _ = \sum_(n <oo) hlength f (A' n))%E; last first.
    apply: (@eq_nneseries _ (hlength f \o A) (hlength f \o A')) => k.
    rewrite /= /A' AE; case: ifPn => // bn.
    by rewrite set_itv_ge//= bnd_simp -leNgt.
  apply (h b').
  - move=> k; rewrite /A'; case: ifPn => // bk.
    by rewrite set_itv_ge//= bnd_simp -leNgt /b' bk.
  - by rewrite AE /b' (negbTE bk).
  - apply: (subset_trans lebig); apply subset_bigcup => k _.
    rewrite /A' AE; case: ifPn => bk //.
    by rewrite subset0 set_itv_ge//= bnd_simp -leNgt.
  - by move=> k; rewrite /b'; case: ifPn => //; rewrite -ltNge => /ltW.
apply: lee_adde => e.
rewrite [e%:num]splitr [in leRHS]EFinD addeA -lee_subl_addr//.
apply: le_trans (epsilon_trick _ _ _) => //=.
have [c ce] := nondecreasing_right_continuousP a.1 ndf rcf [gt0 of e%:num / 2].
have [D De] : exists D : nat -> {posnum R}, forall i,
    f ((b i).2 + (D i)%:num) <= f ((b i).2) + (e%:num / 2) / 2 ^ i.+1.
  suff : forall i, exists di : {posnum R},
      f ((b i).2 + di%:num) <= f ((b i).2) + (e%:num / 2) / 2 ^ i.+1.
    by move/choice => -[g hg]; exists g.
  move=> k; apply nondecreasing_right_continuousP => //.
  by rewrite divr_gt0 // exprn_gt0.
have acbd : `[ a.1 + c%:num / 2, a.2] `<=` \bigcup_i `](b i).1, (b i).2 + (D i)%:num[%classic.
  apply (@subset_trans _ `]a.1, a.2]).
    move=> r; rewrite /= !in_itv/= => /andP [+ ->].
    by rewrite andbT; apply: lt_le_trans; rewrite ltr_addl.
  apply (subset_trans lebig) => r [n _ Anr]; exists n => //.
  move: Anr; rewrite AE /= !in_itv/= => /andP [->]/= /le_lt_trans.
  by apply; rewrite ltr_addl.
have := @segment_compact _ (a.1 + c%:num / 2) a.2; rewrite compact_cover.
have obd k : [set: nat] k-> open `](b k).1, ((b k).2 + (D k)%:num)[%classic.
  by move=> _; exact: interval_open.
move=> /(_ _ _ _ obd acbd){obd acbd}.
case=> X _ acXbd.
rewrite -EFinD.
apply: (@le_trans _ _ (\sum_(i <- X) (hlength f `](b i).1, (b i).2]%classic) +
                       \sum_(i <- X) (f ((b i).2 + (D i)%:num)%R - f (b i).2)%:E)%E).
  apply: (@le_trans _ _ (f a.2 - f (a.1 + c%:num / 2))%:E).
    rewrite lee_fin -addrA -opprD ler_sub// (le_trans _ ce)// ndf//.
    by rewrite ler_add2l ler_pdivr_mulr// ler_pmulr// ler1n.
  apply: (@le_trans _ _ (\sum_(i <- X) (f ((b i).2 + (D i)%:num) - f (b i).1)%:E)%E).
    rewrite sumEFin lee_fin hlength_content_sub_fsum//.
      by move=> k kX; rewrite (@le_trans _ _ (b k).2)// ler_addl.
    apply: subset_trans.
      exact/(subset_trans _ acXbd)/subset_itv_oc_cc.
    move=> x [k kX] kx; rewrite -bigcup_fset; exists k => //.
    by move: x kx; exact: subset_itv_oo_oc.
  rewrite addeC -big_split/=; apply: lee_sum => k _.
  by rewrite !(EFinB, hlength_itv_bnd)// addeA subeK.
rewrite -big_split/= nneseries_esum//; last first.
  by move=> k _; rewrite adde_ge0// hlength_ge0'.
rewrite esum_ge//; exists X => //.
rewrite big_seq [in X in (_ <= X)%E]big_seq; apply: lee_sum => k kX.
by rewrite AE lee_add2l// lee_fin ler_subl_addl natrX De.
Qed.

Let gitvs := [the measurableType _ of salgebraType ocitv].

Definition lebesgue_stieltjes_measure :=
  Hahn_ext [the additive_measure _ _ of hlength f : set ocitv_type -> _ ].

End itv_semiRingOfSets.
Arguments lebesgue_stieltjes_measure {R}.

Section lebesgue_stieltjes_measure_itv.
Variables (d : measure_display) (R : realType) (f : R -> R).
Hypotheses (ndf : {homo f : x y / x <= y}) (rcf : right_continuous f).

Let m := lebesgue_stieltjes_measure d f ndf.

Let g : \bar R -> \bar R := EFinf f.

Let lebesgue_stieltjes_measure_itvoc (a b : R) :
  (m `]a, b] = hlength f `]a, b])%classic.
Proof.
rewrite /m /lebesgue_stieltjes_measure /= /Hahn_ext measurable_mu_extE//; last first.
  by exists (a, b).
exact: hlength_sigma_sub_additive.
Qed.

Lemma set1Ebigcap (x : R) : [set x] = \bigcap_k `](x - k.+1%:R^-1)%R, x]%classic.
Proof.
apply/seteqP; split => [_ -> k _ /=|].
  by rewrite in_itv/= lexx andbT ltr_subl_addl ltr_addr invr_gt0.
move=> y h; apply/eqP/negPn/negP => yx.
red in h.
simpl in h.
Admitted.

Let lebesgue_stieltjes_measure_set1 (a : R) :
  m [set a] = ((f a)%:E - (lim (f @ at_left a))%:E)%E.
Proof.
rewrite (set1Ebigcap a).
Admitted.

Let lebesgue_stieltjes_measure_itvoo (a b : R) : a <= b ->
  m `]a, b[%classic = ((lim (f @ at_left b))%:E - (f a)%:E)%E.
Proof.
Admitted.

Let lebesgue_stieltjes_measure_itvcc (a b : R) : a <= b ->
  m `[a, b]%classic = ((f b)%:E - (lim (f @ at_left a))%:E)%E.
Proof.
Admitted.

Let lebesgue_stieltjes_measure_itvco (a b : R) : a <= b ->
  m `[a, b[%classic = ((lim (f @ at_left b))%:E - (lim (f @ at_left a))%:E)%E.
Proof.
Admitted.


End lebesgue_stieltjes_measure_itv.
