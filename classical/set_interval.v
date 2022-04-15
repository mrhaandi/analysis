(* -*- company-coq-local-symbols: (("`&`" . ?∩) ("`|`" . ?∪) ("set0" . ?∅)); -*- *)
(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrnum interval.
Require Import mathcomp_extra boolp classical_sets.

(******************************************************************************)
(* This files contains lemmas about sets and intervals.                       *)
(*                                                                            *)
(*              neitv i == the interval i is non-empty                        *)
(*                         when the support type is a numFieldType, this      *)
(*                         is equivalent to (i.1 < i.2)%O (lemma neitvE)      *)
(*   set_itv_infty_set0 == multirule to simplify empty intervals              *)
(*             set_itvE == multirule to turn intervals into inequalities      *)
(*     disjoint_itv i j == intervals i and j are disjoint                     *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* definitions and lemmas to make a bridge between MathComp intervals and     *)
(* classical sets                                                             *)
Section set_itv_porderType.
Variables (d : unit) (T : porderType d).
Implicit Types (i j : interval T) (x y : T) (a : itv_bound T).

Definition neitv i := [set` i] != set0.

Lemma neitv_lt_bnd i : neitv i -> (i.1 < i.2)%O.
Proof.
case: i => a b; apply: contraNT => /= /itv_ge ab0.
by apply/eqP; rewrite predeqE => t; split => //=; rewrite ab0.
Qed.

Lemma set_itvP i j : [set` i] = [set` j] :> set _ <-> i =i j.
Proof.
split => [ij x|ij]; first by have /(congr1 (@^~ x))/=/is_true_inj := ij.
by rewrite predeqE => r /=; rewrite ij.
Qed.

Lemma subset_itvP i j : {subset i <= j} <-> [set` i] `<=` [set` j].
Proof. by []. Qed.

Lemma set_itvoo x y : `]x, y[%classic = [set z | (x < z < y)%O].
Proof. by []. Qed.

Lemma set_itvco x y : `[x, y[%classic = [set z | (x <= z < y)%O].
Proof. by []. Qed.

Lemma set_itvcc x y : `[x, y]%classic = [set z | (x <= z <= y)%O].
Proof. by []. Qed.

Lemma set_itvoc x y : `]x, y]%classic = [set z | (x < z <= y)%O].
Proof. by []. Qed.

Lemma set_itv1 x : `[x, x]%classic = [set x].
Proof. by apply/seteqP; split=> y /=; rewrite itvxx ?inE (rwP eqP). Qed.

Lemma set_itvoo0 x : `]x, x[%classic = set0.
Proof. by rewrite -subset0 => y /=; rewrite itv_ge//= bnd_simp ltxx. Qed.

Lemma set_itvoc0 x : `]x, x]%classic = set0.
Proof. by rewrite -subset0 => y /=; rewrite itv_ge//= bnd_simp ltxx. Qed.

Lemma set_itvco0 x : `[x, x[%classic = set0.
Proof. by rewrite -subset0 => y /=; rewrite itv_ge//= bnd_simp ltxx. Qed.

Lemma set_itv_infty_infty : `]-oo, +oo[%classic = @setT T.
Proof. by rewrite predeqE. Qed.

Lemma set_itv_o_infty x : `]x, +oo[%classic = [set z | (x < z)%O].
Proof. by rewrite predeqE => r /=; rewrite in_itv andbT. Qed.

Lemma set_itv_c_infty x : `[x, +oo[%classic = [set z | (x <= z)%O].
Proof. by rewrite predeqE /mkset => r; rewrite in_itv andbT. Qed.

Lemma set_itv_infty_o x : `]-oo, x[%classic = [set z | (z < x)%O].
Proof. by rewrite predeqE /mkset => r; rewrite in_itv. Qed.

Lemma set_itv_infty_c x : `]-oo, x]%classic = [set z | (z <= x)%O].
Proof. by rewrite predeqE /mkset => r; rewrite in_itv. Qed.

Lemma set_itv_pinfty_bnd a : [set` Interval +oo%O a] = set0.
Proof. by apply/eqP/negPn/negP => /neitv_lt_bnd. Qed.

Lemma set_itv_bnd_ninfty a : [set` Interval a -oo%O] = set0.
Proof. by apply/eqP/negPn/negP => /neitv_lt_bnd /=; case: a => [[]a|[]]. Qed.

Definition set_itv_infty_set0 := (set_itv_bnd_ninfty, set_itv_pinfty_bnd).

Definition set_itvE := (set_itv1, set_itvoo0, set_itvoc0, set_itvco0, set_itvoo,
  set_itvcc, set_itvoc, set_itvco, set_itv_infty_infty, set_itv_o_infty,
  set_itv_c_infty, set_itv_infty_o, set_itv_infty_c, set_itv_infty_set0).

Lemma setUitv1 (a : itv_bound T) (x : T) : (a <= BLeft x)%O ->
  [set` Interval a (BLeft x)] `|` [set x] = [set` Interval a (BRight x)].
Proof.
move=> ax; apply/predeqP => z /=; rewrite itv_splitU1// [in X in _ <-> X]inE.
by rewrite (rwP eqP) (rwP orP) orbC.
Qed.

Lemma setU1itv (a : itv_bound T) (x : T) : (BRight x <= a)%O ->
  x |` [set` Interval (BRight x) a] = [set` Interval (BLeft x) a].
Proof.
move=> ax; apply/predeqP => z /=; rewrite itv_split1U// [in X in _ <-> X]inE.
by rewrite (rwP eqP) (rwP orP) orbC.
Qed.

End set_itv_porderType.
Arguments neitv {d T} _.

Section set_itv_latticeType.
Variables (d : unit) (T : latticeType d).
Implicit Types (i j : interval T) (x y : T) (a : itv_bound T).

Lemma set_itvI i j :  [set` (i `&` j)%O] = [set` i] `&` [set` j].
Proof. by apply/seteqP; split=> x /=; rewrite in_itvI (rwP andP). Qed.

End set_itv_latticeType.

Section set_itv_numFieldType.
Variable R : numFieldType.
Implicit Types i : interval R.

Lemma neitvE i : neitv i = (i.1 < i.2)%O.
Proof.
apply/idP/idP; first exact: neitv_lt_bnd.
by move=> /mem_miditv ii; apply/set0P; exists (miditv i).
Qed.

Lemma neitvP i : reflect (i.1 < i.2)%O (neitv i).
Proof. by apply: (iffP idP); rewrite -neitvE. Qed.

End set_itv_numFieldType.

Lemma setitv0 (R : realDomainType) : [set` (0%O : interval R)] = set0.
Proof. by rewrite predeqE. Qed.

Section interval_has_bound.
Variable R : numDomainType.

Lemma has_lbound_itv (x : R) b (a : itv_bound R) :
  has_lbound [set` Interval (BSide b x) a].
Proof. by case: b; exists x => r /andP[]; rewrite bnd_simp // => /ltW. Qed.

Lemma has_ubound_itv (x : R) b (a : itv_bound R) :
  has_ubound [set` Interval a (BSide b x)].
Proof. by case: b; exists x => r /andP[]; rewrite bnd_simp // => _ /ltW. Qed.

End interval_has_bound.

Section subr_image.
Variable R : numDomainType.
Implicit Types E : set R.
Implicit Types x : R.

Lemma setNK : involutive (fun E => -%R @` E).
Proof.
move=> F; rewrite predeqE => y; split => [|Fy].
  by case=> z -[u xu <-{z} <-{y}]; rewrite opprK.
by exists (- y); rewrite ?opprK //; exists y.
Qed.

Lemma lb_ubN E x : lbound E x <-> ubound (-%R @` E) (- x).
Proof.
split=> [/lbP xlbE|/ubP xlbE].
by apply/ubP=> y [z Ez <-{y}]; rewrite ler_oppr opprK; apply xlbE.
by apply/lbP => y Ey; rewrite -(opprK x) ler_oppl; apply xlbE; exists y.
Qed.

Lemma ub_lbN E x : ubound E x <-> lbound (-%R @` E) (- x).
Proof.
split=> [? | /lb_ubN].
by apply/lb_ubN; rewrite opprK setNK.
by rewrite opprK setNK.
Qed.

Lemma has_lb_ubN E : has_lbound E <-> has_ubound (-%R @` E).
Proof.
by split=> [[x /lb_ubN] | [x /ub_lbN]]; [|rewrite setNK]; exists (- x).
Qed.

End subr_image.

Section interval_hasNbound.
Variable R : realDomainType.
Implicit Types E : set R.
Implicit Types x : R.

Lemma has_ubPn {E} : ~ has_ubound E <-> (forall x, exists2 y, E y & x < y).
Proof.
split; last first.
  move=> h [x] /ubP hle; case/(_ x): h => y /hle.
  by rewrite leNgt => /negbTE ->.
move/forallNP => h x; have {h} := h x.
move=> /ubP /existsNP => -[y /not_implyP[Ey /negP]].
by rewrite -ltNge => ltx; exists y.
Qed.

Lemma has_lbPn E : ~ has_lbound E <-> (forall x, exists2 y, E y & y < x).
Proof.
split=> [/has_lb_ubN /has_ubPn NEnub x|Enlb /has_lb_ubN].
  have [y ENy ltxy] := NEnub (- x); exists (- y); rewrite 1?ltr_oppl //.
  by case: ENy => z Ez <-; rewrite opprK.
apply/has_ubPn => x; have [y Ey ltyx] := Enlb (- x).
exists (- y); last by rewrite ltr_oppr.
by exists y => //; rewrite opprK.
Qed.

Lemma hasNlbound_itv (a : itv_bound R) : a != -oo%O ->
  ~ has_lbound [set` Interval -oo%O a].
Proof.
move: a => [b r|[|]] _ //.
  suff: ~ has_lbound `]-oo, r[%classic.
    by case: b => //; apply/contra_not/subset_has_lbound => x /ltW.
  apply/has_lbPn => x; exists (minr (r - 1) (x - 1)).
    by rewrite !set_itvE/= lt_minl ltr_subl_addr ltr_addl ltr01.
  by rewrite lt_minl orbC ltr_subl_addr ltr_addl ltr01.
case=> r /(_ (r - 1)) /=; rewrite in_itv /= => /(_ erefl).
by apply/negP; rewrite -ltNge ltr_subl_addr ltr_addl.
Qed.

Lemma hasNubound_itv (a : itv_bound R) : a != +oo%O ->
  ~ has_ubound [set` Interval a +oo%O].
Proof.
move: a => [b r|[|]] _ //.
  suff: ~ has_ubound `]r, +oo[%classic.
    case: b => //; apply/contra_not/subset_has_ubound => x.
    by rewrite !set_itvE => /ltW.
  apply/has_ubPn => x; rewrite !set_itvE; exists (maxr (r + 1) (x + 1));
  by rewrite ?in_itv /= ?andbT lt_maxr ltr_addl ltr01 // orbT.
case=> r /(_ (r + 1)) /=; rewrite in_itv /= => /(_ erefl).
by apply/negP; rewrite -ltNge ltr_addl.
Qed.

End interval_hasNbound.

#[global] Hint Extern 0 (has_lbound _) => solve[apply: has_lbound_itv] : core.
#[global] Hint Extern 0 (has_ubound _) => solve[apply: has_ubound_itv] : core.
#[global]
Hint Extern 0 (~ has_lbound _) => solve[by apply: hasNlbound_itv] : core.
#[global]
Hint Extern 0 (~ has_ubound _) => solve[by apply: hasNubound_itv] : core.

Lemma opp_itv_bnd_infty (R : numDomainType) (x : R) b :
  -%R @` [set` Interval (BSide b x) +oo%O] =
  [set` Interval -oo%O (BSide (negb b) (- x))].
Proof.
rewrite predeqE => /= r; split=> [[y xy <-]|xr].
  by case: b xy; rewrite !in_itv/= andbT (ler_opp2, ltr_opp2).
exists (- r); rewrite ?opprK //.
by case: b xr; rewrite !in_itv/= andbT (ler_oppr, ltr_oppr).
Qed.

Lemma opp_itvoo (R : numDomainType) (x y : R) :
  -%R @` `]x, y[%classic = `](- y), (- x)[%classic.
Proof.
rewrite predeqE => /= r; split => [[{}r + <-]|].
  by rewrite !in_itv/= !ltr_opp2 andbC.
by exists (- r); rewrite ?opprK// !in_itv/= ltr_oppl ltr_oppr andbC.
Qed.

(* lemmas between itv and set-theoretic operations *)
Section set_itv_porderType.
Variables (d : unit) (T : orderType d).
Implicit Types (a : itv_bound T) (x y : T) (i j : interval T) (b : bool).

Lemma setCitvl a : ~` [set` Interval -oo%O a] = [set` Interval a +oo%O].
Proof. by apply/predeqP => y /=; rewrite -predC_itvl (rwP negP). Qed.

Lemma setCitvr a : ~` [set` Interval a +oo%O] = [set` Interval -oo%O a].
Proof. by rewrite -setCitvl setCK. Qed.

Lemma set_itv_splitI i : [set` i] = [set` Interval i.1 +oo%O] `&` [set` Interval -oo%O i.2].
Proof.
case: i => [a a']; apply/predeqP=> x/=.
by rewrite [in X in X <-> _]itv_splitI (rwP andP).
Qed.

Lemma setCitv i :
  ~` [set` i] = [set` Interval -oo%O i.1] `|` [set` Interval i.2 +oo%O].
Proof.
by apply/predeqP => x /=; rewrite (rwP orP) (rwP negP) [x \notin i]predC_itv.
Qed.

Lemma set_itv_splitD i :
  [set` i] = [set` Interval i.1 +oo%O] `\` [set` Interval i.2 +oo%O].
Proof. by rewrite set_itv_splitI/= setDE setCitvr. Qed.

End set_itv_porderType.

Lemma set_itv_ge [disp : unit] [T : porderType disp] [b1 b2 : itv_bound T] :
  ~~ (b1 < b2)%O -> [set` Interval b1 b2] = set0.
Proof. by move=> Nb12; rewrite -subset0 => x /=; rewrite itv_ge. Qed.

Lemma trivIset_set_itv_nth (R : numDomainType) def (s : seq (interval R))
  (D : set nat) : [set` def] = set0 ->
  trivIset D (fun i => [set` nth def s i]) <->
    trivIset D (fun i => nth set0 [seq [set` j] | j <- s] i).
Proof.
move=> def0; split=> /trivIsetP ss; apply/trivIsetP => i j Di Dj ij.
- have [si|si] := ltP i (size s); last first.
    by rewrite (nth_default set0) ?size_map// set0I.
  have [sj|sj] := ltP j (size s); last first.
    by rewrite setIC (nth_default set0) ?size_map// set0I.
  by rewrite (nth_map def) // (nth_map def) // ss.
- have [?|h] := ltP i (size s); last by rewrite (nth_default def h) def0 set0I.
  have [?|h] := ltP j (size s); last by rewrite (nth_default def h) def0 setI0.
  by have := ss _ _ Di Dj ij; rewrite (nth_map def) // (nth_map def).
Qed.
Arguments trivIset_set_itv_nth {R} _ {s}.

Section disjoint_itv.
Context {R : numDomainType}.

Definition disjoint_itv : rel (interval R) :=
  fun a b => [disjoint [set` a] & [set` b]].

Lemma disjoint_itvxx (i : interval R) : neitv i -> ~~ disjoint_itv i i.
Proof. by move=> i0; rewrite /disjoint_itv/= /disj_set /= setIid. Qed.

Lemma lt_disjoint (i j : interval R) :
  (forall x y, x \in i -> y \in j -> x < y) -> disjoint_itv i j.
Proof.
move=> ij; apply/eqP; rewrite predeqE => x; split => // -[xi xj].
by have := ij _ _ xi xj; rewrite ltxx.
Qed.

End disjoint_itv.

Lemma disjoint_neitv {R : realFieldType} (i j : interval R) :
  disjoint_itv i j <-> ~~ neitv (itv_meet i j).
Proof.
case: i j => [a b] [c d]; rewrite /disjoint_itv/disj_set /= -set_itvI.
by split => [/negPn//|?]; apply/negPn.
Qed.

Lemma neitv_bnd1 (R : numFieldType) (s : seq (interval R)) :
  all neitv s -> forall i, i \in s -> i.1 != +oo%O.
Proof.
move=> /allP sne [a b] si /=; apply/negP => /eqP boo; move: si.
by rewrite boo => /sne /negP; apply; rewrite set_itv_infty_set0.
Qed.

Lemma neitv_bnd2 (R : numFieldType) (s : seq (interval R)) :
  all neitv s -> forall i, i \in s -> i.2 != -oo%O.
Proof.
move=> /allP sne [a b] si /=; apply/negP => /eqP boo; move: si.
by rewrite boo => /sne /negP; apply; rewrite set_itv_infty_set0.
Qed.
