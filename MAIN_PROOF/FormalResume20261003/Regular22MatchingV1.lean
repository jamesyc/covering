import FormalResume20261003.LowPairProfileV1
import campaign_next15.lean.d0_lift.SlotPairsV2

/-! Elementary physical matching lemma. The proof splits actual row slots at
three distinct points and uses the 9 by 10 cross-grid obstruction. It has no
spectral premise and no dependency on a finite signature catalogue. -/
namespace Covering.NormalizedBridge20261003.Regular22Matching

open PointSplit PointDegree TwoPointSplit SideLift

theorem cast_of_ne_last {n : Nat} (p : Fin (n+1)) (hp : p≠Fin.last n) :
    ∃ q : Fin n, q.castSucc=p := by
  revert hp
  refine Fin.lastCases ?_ (fun q _ => ⟨q,rfl⟩) p
  intro hn
  exact False.elim (hn rfl)

theorem valid_rows_relabel {n k : Nat} (F : Family n) (e d : Fin n → Fin n)
    (he : ∀ p, d (e p)=p) (hrows : ∀ R, R ∈ F → ValidBlock k R) :
    ∀ R, R ∈ relabelFamily e F → ValidBlock k R := by
  intro R hR
  obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hR
  exact (validBlock_relabel_iff e d he S).mpr (hrows S hS)

/-- A six-row pair cover on 21 points with row size 11 has at most one
point of degree two. Duplicate row slots are allowed. -/
theorem no_two_low_in_pair_cover (F : Family 21)
    (hrows : ∀ R, R ∈ F → ValidBlock 11 R) (hcover : IsCovering 2 F)
    (hlen : F.length=6) (p q : Fin 21) (hpq : p≠q)
    (hp : degree F p=2) (hq : degree F q=2) : False := by
  let e := swapPoint p (Fin.last 20)
  have he : ∀ x, e (e x)=x := swapPoint_involutive p (Fin.last 20)
  have heLast : e (Fin.last 20)=p := swapPoint_right p (Fin.last 20)
  let G := relabelFamily e F
  have hGrows := valid_rows_relabel F e e he hrows
  have hGcover : IsCovering 2 G := (isCovering_relabel_iff e e he he F).mpr hcover
  have hGlen : G.length=6 := by simpa [G,relabelFamily] using hlen
  have hGp : degree G (Fin.last 20)=2 := by
    rw [degree_relabel e e he he,heLast]
    exact hp
  have hGq : degree G (e q)=2 := by
    rw [degree_relabel e e he he,he]
    exact hq
  have hqne : e q≠Fin.last 20 := by
    intro hh
    have hh' := congrArg e hh
    rw [he,heLast] at hh'
    exact hpq hh'.symm
  obtain ⟨r,hr⟩ := cast_of_ne_last (e q) hqne
  let T := through G
  let U := away G
  have hTrows : ∀ R, R ∈ T → ValidBlock 10 R := through_valid G hGrows
  have hUrows : ∀ R, R ∈ U → ValidBlock 11 R := away_valid G hGrows
  have hTcover : IsCovering 1 T := (covering_split G hGcover).1
  have hTUcover : IsCovering 2 (T++U) := (covering_split G hGcover).2
  have hTlen : T.length=2 := by rw [through_length]; exact hGp
  have hTUlen : T.length+U.length=6 := by rw [split_length]; exact hGlen
  have hdegree : degree T r+degree U r=2 := by
    rw [degree_split_old,hr]
    exact hGq
  let d := swapPoint r (Fin.last 19)
  have hd : ∀ x, d (d x)=x := swapPoint_involutive r (Fin.last 19)
  have hdLast : d (Fin.last 19)=r := swapPoint_right r (Fin.last 19)
  let V := relabelFamily d T
  let W := relabelFamily d U
  have hVrows := valid_rows_relabel T d d hd hTrows
  have hWrows := valid_rows_relabel U d d hd hUrows
  have hVcover : IsCovering 1 V := (isCovering_relabel_iff d d hd hd T).mpr hTcover
  have hVWcover : IsCovering 2 (V++W) := by
    have hh := (isCovering_relabel_iff d d hd hd (T++U)).mpr hTUcover
    simpa [V,W,relabelFamily,List.map_append] using hh
  have hVlen : V.length=2 := by simpa [V,relabelFamily] using hTlen
  have hVWlen : V.length+W.length=6 := by simpa [V,W,relabelFamily] using hTUlen
  have hVWdegree : degree V (Fin.last 19)+degree W (Fin.last 19)=2 := by
    rw [degree_relabel d d hd hd,degree_relabel d d hd hd,hdLast]
    exact hdegree
  apply low_profile_impossible (through V) (away V) (through W) (away W)
  refine ⟨?_,?_,?_,through_valid V hVrows,away_valid V hVrows,
    through_valid W hWrows,away_valid W hWrows,(covering_split V hVcover).1,
    (covering_split V hVcover).2,?_,?_⟩
  · have hv := split_length V
    have hw := split_length W
    omega
  · rw [split_length]
    exact hVlen
  · simpa only [through_length,degree] using hVWdegree
  · simpa only [TwoPointSplit.through_append] using (covering_split (V++W) hVWcover).1
  · simpa only [TwoPointSplit.through_append,TwoPointSplit.away_append] using
      (covering_split (V++W) hVWcover).2

/-- In a uniform (22,12,3) cover, a point appearing in six rows cannot
have two distinct partners of codegree two. This includes every point of a
6-regular slice on 22 points. -/
theorem codegree_two_matching (F : Family 22)
    (hrows : ∀ R, R ∈ F → ValidBlock 12 R) (hcover : IsCovering 3 F)
    (u v w : Fin 22) (huv : u≠v) (huw : u≠w)
    (hu : degree F u=6) (hv : pairDegree F u v=2) (hw : pairDegree F u w=2) : v=w := by
  apply Classical.byContradiction
  intro hvw
  let e := swapPoint u (Fin.last 21)
  have he : ∀ x, e (e x)=x := swapPoint_involutive u (Fin.last 21)
  have heLast : e (Fin.last 21)=u := swapPoint_right u (Fin.last 21)
  let G := relabelFamily e F
  have hGrows := valid_rows_relabel F e e he hrows
  have hGcover : IsCovering 3 G := (isCovering_relabel_iff e e he he F).mpr hcover
  have hne (x : Fin 22) (hux : u≠x) : e x≠Fin.last 21 := by
    intro hh
    have hh' := congrArg e hh
    rw [he,heLast] at hh'
    exact hux hh'.symm
  obtain ⟨p,hp⟩ := cast_of_ne_last (e v) (hne v huv)
  obtain ⟨q,hq⟩ := cast_of_ne_last (e w) (hne w huw)
  have hpq : p≠q := by
    intro hh
    have hh' : e v=e w := hp.symm.trans ((congrArg Fin.castSucc hh).trans hq)
    have hh'' := congrArg e hh'
    rw [he,he] at hh''
    exact hvw hh''
  have hlen : (through G).length=6 := by
    rw [through_length]
    change degree G (Fin.last 21)=6
    rw [degree_relabel e e he he,heLast]
    exact hu
  have hpd : degree (through G) p=2 := by
    rw [degree_through,hp,pair_degree_relabel e e he he,heLast,he]
    exact hv
  have hqd : degree (through G) q=2 := by
    rw [degree_through,hq,pair_degree_relabel e e he he,heLast,he]
    exact hw
  exact no_two_low_in_pair_cover (through G) (through_valid G hGrows)
    (covering_split G hGcover).1 hlen p q hpq hpd hqd

end Covering.NormalizedBridge20261003.Regular22Matching
