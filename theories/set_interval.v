(* -*- company-coq-local-symbols: (("`&`" . ?∩) ("`|`" . ?∪) ("set0" . ?∅)); -*- *)
(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import finmap fingroup perm rat.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.classical Require Export set_interval.
Require Import reals ereal signed topology.
Require Import mathcomp_extra normedtype.
From HB Require Import structures.
Require Import sequences.

(******************************************************************************)
(* This files contains lemmas about sets and intervals on reals.              *)
(*                                                                            *)
(*         conv, ndconv == convexity operator                                 *)
(*         factor a b x := (x - a) / (b - a)                                  *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
(* Import numFieldTopology.Exports. *)

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section interval_has.
Variable R : realType.
Implicit Types x : R.

Lemma has_sup_half x b (i : itv_bound R) : (i < BSide b x)%O ->
  has_sup [set` Interval i (BSide b x)].
Proof.
move: b i => [] [[]y|[]]; rewrite ?bnd_simp => xy; split=> //; do 1?[
  by exists ((x + y) / 2); rewrite !set_itvE/= addrC !(midf_le,midf_lt) //;
    exact: ltW
| by exists (x - 1); rewrite !set_itvE/=
    !(ltr_subl_addr, ler_subl_addr, ltr_addl,ler_addl)].
Qed.

Lemma has_inf_half x b (i : itv_bound R) : (BSide b x < i)%O ->
  has_inf [set` Interval (BSide b x) i].
Proof.
move: b i => [] [[]y|[]]; rewrite ?bnd_simp => xy; do 1?[
  by split=> //; exists ((x + y) / 2);
     rewrite !set_itvE/= !(midf_le,midf_lt) //;
     exact: ltW
 | by split => //; exists (x + 1); rewrite !set_itvE/= !(ltr_addl,ler_addl)].
Qed.

End interval_has.

#[global]
Hint Extern 0 (has_sup _) => solve[apply: has_sup1 | exact: has_sup_half] : core.
#[global]
Hint Extern 0 (has_inf _) => solve[apply: has_inf1 | exact: has_inf_half]: core.

Section interval_sup_inf.
Variable R : realType.
Implicit Types x y : R.

Let sup_itv_infty_bnd x b : sup [set` Interval -oo%O (BSide b x)] = x.
Proof.
case: b; last first.
  by rewrite -setUitv1// sup_setU ?sup1// => ? ? ? ->; exact/ltW.
set s := sup _; apply/eqP; rewrite eq_le; apply/andP; split.
- apply sup_le_ub; last by move=> ? /ltW.
  by exists (x - 1); rewrite !set_itvE/= ltr_subl_addr ltr_addl.
- rewrite leNgt; apply/negP => sx; pose p := (s + x) / 2.
  suff /andP[?]: (p < x) && (s < p) by apply/negP; rewrite -leNgt sup_ub.
  by rewrite !midf_lt.
Qed.

Let inf_itv_bnd_infty x b : inf [set` Interval (BSide b x) +oo%O] = x.
Proof.
case: b; last by rewrite /inf opp_itv_bnd_infty sup_itv_infty_bnd opprK.
rewrite -setU1itv// inf_setU ?inf1// => _ b ->.
by rewrite !set_itvE => /ltW.
Qed.

Let sup_itv_o_bnd x y b : x < y ->
  sup [set` Interval (BRight x) (BSide b y)] = y.
Proof.
case: b => xy; last first.
  by rewrite -setUitv1// sup_setU ?sup1// => ? ? /andP[? /ltW ?] ->.
set B := [set` _]; set A := `]-oo, x]%classic.
rewrite -(@sup_setU _ A B) //.
- rewrite -(sup_itv_infty_bnd y true); congr sup.
  rewrite predeqE => u; split=> [[|/andP[]//]|yu].
  by rewrite /A !set_itvE => /le_lt_trans; apply.
  by have [xu|ux] := ltP x u; [right; rewrite /B !set_itvE/= xu| left].
- by move=> u v; rewrite /A /B => ? /andP[xv _]; rewrite (le_trans _ (ltW xv)).
Qed.

Let sup_itv_bounded x y a b : (BSide a x < BSide b y)%O ->
  sup [set` Interval (BSide a x) (BSide b y)] = y.
Proof.
case: a => xy; last exact: sup_itv_o_bnd.
case: b in xy *.
  by rewrite -setU1itv// sup_setU ?sup_itv_o_bnd// => ? ? -> /andP[/ltW].
by rewrite -setUitv1// sup_setU ?sup1// => ? ? /andP[_ /ltW ? ->].
Qed.

Let inf_itv_bnd_o x y b : (BSide b x < BLeft y)%O ->
  inf [set` Interval (BSide b x) (BLeft y)] = x.
Proof.
case: b => xy.
  by rewrite -setU1itv// inf_setU ?inf1// => _ ? -> /andP[/ltW].
by rewrite /inf opp_itvoo sup_itv_o_bnd ?opprK // ltr_oppl opprK.
Qed.

Let inf_itv_bounded x y a b : (BSide a x < BSide b y)%O ->
  inf [set` Interval (BSide a x) (BSide b y)] = x.
Proof.
case: b => xy; first exact: inf_itv_bnd_o.
case: a in xy *.
  by rewrite -setU1itv// inf_setU ?inf1// => ? ? -> /andP[/ltW].
by rewrite -setUitv1// inf_setU ?inf_itv_bnd_o// => ? ? /andP[? /ltW ?] ->.
Qed.

Lemma sup_itv a b x : (a < BSide b x)%O ->
  sup [set` Interval a (BSide b x)] = x.
Proof. by case: a => [b' y|[]]; rewrite ?bnd_simp//= => /sup_itv_bounded->. Qed.

Lemma inf_itv a b x : (BSide b x < a)%O ->
  inf [set` Interval (BSide b x) a] = x.
Proof. by case: a => [b' y|[]]; rewrite ?bnd_simp//= => /inf_itv_bounded->. Qed.

Lemma sup_itvcc x y : x <= y -> sup `[x, y] = y.
Proof. by move=> *; rewrite sup_itv. Qed.

Lemma inf_itvcc x y : x <= y -> inf `[x, y] = x.
Proof. by move=> *; rewrite inf_itv. Qed.

End interval_sup_inf.

Section set_itv_realType.
Variable R : realType.
Implicit Types x : R.

Lemma set_itvK : {in neitv, cancel pred_set (@Rhull R)}.
Proof.
move=> [[[] x|[]] [[] y|[]]] /neitvP //;
  rewrite /Rhull /= !(in_itv, inE)/= ?bnd_simp => xy.
- rewrite asboolT// inf_itv// lexx/= xy asboolT// asboolT//=.
  by rewrite asboolF//= sup_itv//= ltxx ?andbF.
- by rewrite asboolT// inf_itv// ?asboolT// ?sup_itv// ?lexx ?xy.
- by rewrite asboolT//= inf_itv// lexx asboolT// asboolF.
- rewrite asboolT// inf_itv//= ltxx asboolF// asboolT//.
  by rewrite sup_itv// ltxx andbF asboolF.
  rewrite asboolT // inf_itv // ltxx asboolF // asboolT //.
  by rewrite sup_itv // xy lexx asboolT.
- by rewrite asboolT // inf_itv// ltxx asboolF // asboolF.
- by rewrite asboolF // asboolT // sup_itv// ltxx asboolF.
- by rewrite asboolF // asboolT // sup_itv// lexx asboolT.
- by rewrite asboolF // asboolF.
Qed.

Lemma RhullT : Rhull setT = `]-oo, +oo[%R :> interval R.
Proof. by rewrite /Rhull -set_itv_infty_infty asboolF// asboolF. Qed.

Lemma RhullK : {in (@is_interval _ : set (set R)), cancel (@Rhull R) pred_set}.
Proof. by move=> X /asboolP iX; apply/esym/is_intervalP. Qed.

Lemma itv_c_inftyEbigcap x :
  `[x, +oo[%classic = \bigcap_k `]x - k.+1%:R^-1, +oo[%classic.
Proof.
rewrite predeqE => y; split=> /= [|xy].
  rewrite in_itv /= andbT => xy z _ /=; rewrite in_itv /= andbT ltr_subl_addr.
  by rewrite (le_lt_trans xy) // ltr_addl invr_gt0 ltr0n.
rewrite in_itv /= andbT leNgt; apply/negP => yx.
have {}[k ykx] := ltr_add_invr yx.
have {xy}/= := xy k Logic.I.
by rewrite in_itv /= andbT; apply/negP; rewrite -leNgt ler_subr_addr ltW.
Qed.

Lemma itv_bnd_inftyEbigcup b x : [set` Interval (BSide b x) +oo%O] =
  \bigcup_k [set` Interval (BSide b x) (BLeft k%:R)].
Proof.
rewrite predeqE => y; split=> /=; last first.
  by move=> [n _]/=; rewrite in_itv => /andP[xy yn]; rewrite in_itv /= xy.
rewrite in_itv /= andbT => xy; exists (`|floor y|%N.+1) => //=.
rewrite in_itv /= xy /= -addn1 natrD.
have [y0|y0] := ltP 0 y; last by rewrite (le_lt_trans y0)// ltr_spaddr.
rewrite natr_absz ger0_norm; last by rewrite floor_ge0 ltW.
by rewrite -RfloorE lt_succ_Rfloor.
Qed.

Lemma itv_o_inftyEbigcup x :
  `]x, +oo[%classic = \bigcup_k `[x + k.+1%:R^-1, +oo[%classic.
Proof.
rewrite predeqE => y; split => [|[n _]]/=.
  rewrite in_itv /= andbT => xy.
  have {}[k xky] := ltr_add_invr xy.
  by exists k => //=; rewrite in_itv /= (ltW xky).
rewrite in_itv /= andbT => xny.
by rewrite in_itv /= andbT (lt_le_trans _ xny) // ltr_addl invr_gt0.
Qed.

Lemma set_itv_setT (i : interval R) : [set` i] = setT -> i = `]-oo, +oo[.
Proof.
have [i0  /(congr1 (@Rhull _))|] := boolP (neitv i).
  by rewrite set_itvK// => ->; exact: RhullT.
by rewrite negbK => /eqP ->; rewrite predeqE => /(_ 0)[_]/(_ Logic.I).
Qed.

End set_itv_realType.

Section conv_Rhull.
Variable R : realType.
Implicit Types (a b t r : R) (A : set R).

Definition conv a b t : R := (1 - t) * a + t * b.

Definition factor a b x := (x - a) / (b - a).

Lemma conv_id : conv 0 1 = id.
Proof. by apply/funext => t; rewrite /conv mulr0 add0r mulr1. Qed.

Lemma convEl a b t : conv a b t = t * (b - a) + a.
Proof. by rewrite /conv mulrBl mul1r mulrBr addrAC [RHS]addrC addrA. Qed.

Lemma convEr a b t : conv a b t = (1 - t) * (a - b) + b.
Proof.
rewrite /conv mulrBr -addrA; congr (_ + _).
by rewrite mulrBl opprB mul1r addrNK.
Qed.

Lemma conv10 t : conv 1 0 t = 1 - t.
Proof. by rewrite /conv mulr0 addr0 mulr1. Qed.

Lemma conv0 a b : conv a b 0 = a.
Proof. by rewrite /conv subr0 mul1r mul0r addr0. Qed.

Lemma conv1 a b : conv a b 1 = b.
Proof. by rewrite /conv subrr mul0r add0r mul1r. Qed.

Lemma conv_sym a b t : conv a b t = conv b a (1 - t).
Proof. by rewrite /conv opprB addrCA subrr addr0 addrC. Qed.

Lemma conv_flat a : conv a a = cst a.
Proof. by apply/funext => t; rewrite convEl subrr mulr0 add0r. Qed.

Lemma factorl a b : factor a b a = 0.
Proof. by rewrite /factor subrr mul0r. Qed.

Lemma factorr a b : a != b -> factor a b b = 1.
Proof. by move=> Nab; rewrite /factor divff// subr_eq0 eq_sym. Qed.

Lemma factor_flat a : factor a a = cst 0.
Proof. by apply/funext => x; rewrite /factor subrr invr0 mulr0. Qed.

Lemma mem_1B_itvcc t : (1 - t \in `[0, 1]) = (t \in `[0, 1]).
Proof. by rewrite !in_itv/= subr_ge0 ger_addl oppr_le0 andbC. Qed.

Lemma factorK a b : a != b -> cancel (factor a b) (conv a b).
Proof. by move=> ? x; rewrite convEl mulfVK ?addrNK// subr_eq0 eq_sym. Qed.

Lemma convK a b : a != b -> cancel (conv a b) (factor a b).
Proof. by move=> ? x; rewrite /factor convEl addrK mulfK// subr_eq0 eq_sym. Qed.

Lemma conv_inj a b : a != b -> injective (conv a b).
Proof. by move/convK/can_inj. Qed.

Lemma factor_inj a b : a != b -> injective (factor a b).
Proof. by move/factorK/can_inj. Qed.

Lemma conv_bij a b : a != b -> bijective (conv a b).
Proof. by move=> ab; apply: Bijective (convK ab) (factorK ab). Qed.

Lemma factor_bij a b : a != b -> bijective (factor a b).
Proof. by move=> ab; apply: Bijective (factorK ab) (convK ab). Qed.

Lemma leW_conv a b : a <= b -> {homo conv a b : x y / x <= y}.
Proof. by move=> ? ? ? ?; rewrite !convEl ler_add ?ler_wpmul2r// subr_ge0. Qed.

Lemma leW_factor a b : a <= b -> {homo factor a b : x y / x <= y}.
Proof.
by move=> ? ? ? ?; rewrite /factor ler_wpmul2r ?ler_add// invr_ge0 subr_ge0.
Qed.

Lemma le_conv a b : a < b -> {mono conv a b : x y / x <= y}.
Proof.
move=> ltab; have leab := ltW ltab.
by apply: homo_mono (convK _) (leW_factor _) (leW_conv _); rewrite // lt_eqF.
Qed.

Lemma le_factor a b : a < b -> {mono factor a b : x y / x <= y}.
Proof.
move=> ltab; have leab := ltW ltab.
by apply: homo_mono (factorK _) (leW_conv _) (leW_factor _); rewrite // lt_eqF.
Qed.

Lemma lt_conv a b : a < b -> {mono conv a b : x y / x < y}.
Proof. by move/le_conv/leW_mono. Qed.

Lemma lt_factor a b : a < b -> {mono factor a b : x y / x < y}.
Proof. by move/le_factor/leW_mono. Qed.

Definition ndconv a b of a < b := conv a b.

Lemma ndconvE a b (ab : a < b) : ndconv ab = conv a b. Proof. by []. Qed.

Let ltNeq a b : a < b -> a != b. Proof. by move=> /lt_eqF->. Qed.

HB.instance Definition _ a b (ab : a < b) :=
  @Can2.Build _ _ setT setT (ndconv ab) (factor a b)
    (fun _ _ => I) (fun _ _ => I)
    (in1W (convK (ltNeq ab))) (in1W (factorK (ltNeq ab))).

Lemma conv_itv_bij ba bb a b : a < b ->
  set_bij [set` Interval (BSide ba 0) (BSide bb 1)]
          [set` Interval (BSide ba a) (BSide bb b)] (conv a b).
Proof.
move=> ltab; rewrite -ndconvE; apply: bij_subr => //=; rewrite setTI ?ndconvE.
apply/predeqP => t /=; rewrite !in_itv/= {1}convEl convEr.
rewrite -lteif_subl_addr subrr -lteif_pdivr_mulr ?subr_gt0// mul0r.
rewrite -lteif_subr_addr subrr -lteif_ndivr_mulr ?subr_lt0// mul0r.
by rewrite lteif_subr_addl addr0.
Qed.

Lemma factor_itv_bij ba bb a b : a < b ->
  set_bij [set` Interval (BSide ba a) (BSide bb b)]
          [set` Interval (BSide ba 0) (BSide bb 1)] (factor a b).
Proof.
move=> ltab; have -> : factor a b = (ndconv ltab)^-1%FUN by [].
by apply/splitbij_sub_sym => //; apply: conv_itv_bij.
Qed.

Lemma mem_conv_itv ba bb a b : a < b ->
  set_fun [set` Interval (BSide ba 0) (BSide bb 1)]
          [set` Interval (BSide ba a) (BSide bb b)] (conv a b).
Proof. by case/(conv_itv_bij ba bb). Qed.

Lemma mem_factor_itv ba bb a b :
  set_fun [set` Interval (BSide ba a) (BSide bb b)]
          [set` Interval (BSide ba 0) (BSide bb 1)] (factor a b).
Proof.
have [|leba] := ltP a b; first by case/(factor_itv_bij ba bb).
move=> x /=; have [|/itv_ge->//] := (boolP (BSide ba a < BSide bb b)%O).
rewrite lteBSide; case: ba bb => [] []//=; rewrite ?le_gtF//.
by case: ltgtP leba => // -> _ _ _; rewrite factor_flat in_itv/= lexx ler01.
Qed.

Lemma mem_conv_itvcc a b : a <= b -> set_fun `[0, 1] `[a, b] (conv a b).
Proof.
rewrite le_eqVlt => /predU1P[<-|]; first by rewrite set_itv1 conv_flat.
by move=> lt_ab; case: (conv_itv_bij true false lt_ab).
Qed.

Lemma range_conv ba bb a b : a < b ->
   conv a b @` [set` Interval (BSide ba 0) (BSide bb 1)] =
               [set` Interval (BSide ba a) (BSide bb b)].
Proof. by move=> /(conv_itv_bij ba bb)/Pbij[f ->]; rewrite image_eq. Qed.

Lemma range_factor ba bb a b : a < b ->
   factor a b @` [set` Interval (BSide ba a) (BSide bb b)] =
                 [set` Interval (BSide ba 0) (BSide bb 1)].
Proof. by move=> /(factor_itv_bij ba bb)/Pbij[f ->]; rewrite image_eq. Qed.

Lemma Rhull_smallest A : [set` Rhull A] = smallest (@is_interval R) A.
Proof.
apply/seteqP; split; last first.
  by apply: smallest_sub; [apply: interval_is_interval | apply: sub_Rhull].
move=> x /= + I [Iitv AI]; rewrite /Rhull.
have [|] := asboolP (has_lbound A) => lA; last first.
  have /forallNP/(_ x)/existsNP[a] := lA.
  move=> /existsNP[Aa /negP]; rewrite -ltNge => ax.
  have [|]:= asboolP (has_ubound A) => uA; last first.
    move=> ?; have /forallNP/(_ x)/existsNP[b] := uA.
    move=> /existsNP[Ab /negP]; rewrite -ltNge => xb.
    have /is_intervalPlt/(_ a b) := Iitv; apply; do ?by apply: AI.
    by rewrite ax xb.
  have [As|NAs]/= := asboolP (A _) => xA.
    by apply: (Iitv a (sup A)); by [apply: AI | rewrite ltW ?ax].
  have [||b Ab xb] := @sup_gt _ A x; do ?by [exists a | rewrite (itvP xA)].
  have /is_intervalPlt/(_ a b) := Iitv; apply; do ?by apply: AI.
  by rewrite ax xb.
have [|]:= asboolP (has_ubound A) => uA; last first.
  have /forallNP/(_ x)/existsNP[b] := uA.
  move=> /existsNP[Ab /negP]; rewrite -ltNge => xb.
  have [Ai|NAi]/= := asboolP (A _) => xA.
    by apply: (Iitv (inf A) b); by [apply: AI | rewrite (ltW xb)].
  have [||a Aa ax] := @inf_lt _ A x; do ?by [exists b | rewrite (itvP xA)].
  have /is_intervalPlt/(_ a b) := Iitv; apply; do ?by apply: AI.
  by rewrite ax xb.
have [Ai|NAi]/= := asboolP (A _); have [As|NAs]/= := asboolP (A _).
- by apply: Iitv; apply: AI.
- move=> xA.
  have [||b Ab xb] := @sup_gt _ A x; do ?by [exists (inf A) | rewrite (itvP xA)].
  have /(_ (inf A) b) := Iitv; apply; do ?by apply: AI.
  by rewrite (itvP xA) (ltW xb).
- move=> xA.
  have [||a Aa ax] := @inf_lt _ A x; do ?by [exists (sup A) | rewrite (itvP xA)].
  have /(_ a (sup A)) := Iitv; apply; do ?by apply: AI.
  by rewrite (itvP xA) (ltW ax).
have [->|/set0P AN0] := eqVneq A set0.
  by rewrite inf0 sup0 itv_ge//= ltBSide/= ltxx.
move=> xA.
have [||a Aa ax] := @inf_lt _ A x; do ?by [|rewrite (itvP xA)].
have [||b Ab xb] := @sup_gt _ A x; do ?by [|rewrite (itvP xA)].
have /is_intervalPlt/(_ a b) := Iitv; apply; do ?by apply: AI.
by rewrite ax xb.
Qed.

Lemma le_Rhull : {homo (@Rhull R) : A B / (A `<=` B) >-> {subset A <= B}}.
Proof.
move=> A B AB; suff: [set` Rhull A] `<=` [set` Rhull B] by [].
rewrite Rhull_smallest; apply: smallest_sub; first exact: interval_is_interval.
by rewrite Rhull_smallest; apply: sub_smallest.
Qed.

Lemma neitv_Rhull A : ~~ neitv (Rhull A) -> A = set0.
Proof.
move/negPn/eqP => A0; rewrite predeqE => r; split => // /sub_Rhull.
by rewrite A0.
Qed.

Lemma Rhull_involutive A : Rhull [set` Rhull A] = Rhull A.
Proof.
have [A0|/neitv_Rhull] := boolP (neitv (Rhull A)); first by rewrite set_itvK.
by move=> ->; rewrite ?Rhull0 set_itvE Rhull0.
Qed.

End conv_Rhull.

Coercion ereal_of_itv_bound T (b : itv_bound T) : \bar T :=
  match b with BSide _ y => y%:E | +oo%O => +oo%E | -oo%O => -oo%E end.
Arguments ereal_of_itv_bound T !b.

Lemma le_bnd_ereal (R : realDomainType) (a b : itv_bound R) :
  (a <= b)%O -> (a <= b)%E.
Proof.
move: a b => -[[] a|[]] [bb b|[]] //=; rewrite ?(leey,leNye)//.
  by rewrite bnd_simp.
by move=> /lteifW.
Qed.

Lemma lt_ereal_bnd (R : realDomainType) (a b : itv_bound R) :
  (a < b)%E -> (a < b)%O.
Proof.
by move: a b => -[[] a|[]] [[] b|[]] //=;
  rewrite ?(lee_pinfty,lee_ninfty,lte_fin)// => ab; rewrite bnd_simp ltW.
Qed.

Lemma Interval_ereal_mem (R : realDomainType) (r : R) (a b : itv_bound R) :
  r \in Interval a b -> (a <= r%:E <= b)%E.
Proof.
case: a b => [[] a|[]] [[] b|[]] => /[dup] rab /itvP rw//=;
by rewrite ?lee_fin ?rw//= ?leey ?leNye//; move: rab; rewrite in_itv//= andbF.
Qed.

Lemma ereal_mem_Interval (R : realDomainType) (r : R) (a b : itv_bound R) :
  (a < r%:E < b)%E -> r \in Interval a b.
Proof.
move: a b => [[]a|[]] [[]b|[]] //=; rewrite ?lte_fin ?in_itv //= => /andP[] //;
by do ?[move->|move/ltW|move=>_].
Qed.

Lemma disj_itv_Rhull {R : realType} (A B : set R) : A `&` B = set0 ->
  is_interval A -> is_interval B -> disjoint_itv (Rhull A) (Rhull B).
Proof.
by move=> AB0 iA iB; rewrite /disjoint_itv RhullK ?inE// RhullK ?inE.
Qed.
