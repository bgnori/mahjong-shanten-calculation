import Shanten.Input37.Validation
import Shanten.Capacity.Overall

namespace Shanten.Input37

lemma normalizedHand_counts_cast (h : Nonnegative input.standing) (tile : Tile) :
    ((normalizedHand input h).counts tile : Int) = normalizeCounts input.standing tile :=
  by
    simp only [normalizedHand]
    rw [DomainAdapter.normalizeCounts_matches_domain]
    apply Int.natCast_toNat_eq_self.mpr
    rw [← DomainAdapter.normalizeCounts_matches_domain]
    exact normalizeCounts_nonneg h tile

lemma normalizedHand_tileCount (h : Nonnegative input.standing) :
    (tileCount (normalizedHand input h) : Int) = standingCount input := by
  simp only [tileCount, Nat.cast_sum]
  simp_rw [normalizedHand_counts_cast h]
  exact normalizeCounts_sum input.standing

private lemma fixedTiles_count (fixed : List Capacity.FixedMeld) (tile : Tile) :
    (Capacity.fixedTiles fixed).count tile =
      (fixed.map fun meld => meld.tiles.count tile).sum := by
  induction fixed with
  | nil => simp [Capacity.fixedTiles]
  | cons meld rest ih => simpa [Capacity.fixedTiles] using congrArg (meld.tiles.count tile + ·) ih

private lemma normalizeCounts_meldCounts (melds : List MeldInput) (tile : Tile) :
    normalizeCounts (meldCounts melds) tile =
      (melds.map fun raw => normalizeCounts raw.tiles tile).sum := by
  induction melds with
  | nil => simp [meldCounts, normalizeCounts]
  | cons raw rest ih => simpa [meldCounts, normalizeCounts_add] using congrArg (normalizeCounts raw.tiles tile + ·) ih

lemma parsedMelds_counts
    (hparsed : ∀ index : Fin input.melds.length,
      (parseMeld input.melds[index]).isSome = true) (tile : Tile) :
    ((Capacity.fixedTiles (parsedMelds input hparsed)).count tile : Int) =
      normalizeCounts (meldCounts input.melds) tile := by
  rw [fixedTiles_count, Nat.cast_list_sum, List.map_map, normalizeCounts_meldCounts]
  apply congrArg List.sum
  calc
    _ = List.ofFn (fun index : Fin input.melds.length =>
        normalizeCounts input.melds[index].tiles tile) := by
      simp only [parsedMelds, List.map_ofFn]
      apply congrArg List.ofFn
      funext index
      exact ((parseMeld_some_matches (Option.some_get (hparsed index)).symm).2 tile).symm
    _ = _ := by
      change List.ofFn ((fun raw => normalizeCounts raw.tiles tile) ∘ input.melds.get) = _
      rw [← List.map_ofFn, List.ofFn_get]

theorem validateAndNormalize_valid
    (hresult : validateAndNormalize input = .ok normalized) :
    Capacity.ValidHand normalized.fixed normalized.hand ∧
      (tileCount normalized.hand + 3 * normalized.fixed.length = 13 ∨
        tileCount normalized.hand + 3 * normalized.fixed.length = 14) := by
  obtain ⟨hvalid, hparsed, rfl⟩ := validateAndNormalize_ok_iff.mp hresult
  change Capacity.ValidHand (parsedMelds input hparsed) (normalizedHand input hvalid.1) ∧
    (tileCount (normalizedHand input hvalid.1) + 3 * (parsedMelds input hparsed).length = 13 ∨
      tileCount (normalizedHand input hvalid.1) + 3 * (parsedMelds input hparsed).length = 14)
  have hlength : (parsedMelds input hparsed).length = input.melds.length := by
    simp [parsedMelds]
  refine ⟨⟨hlength.symm, by rw [hlength]; exact hvalid.2.2.2.1, ?_⟩, ?_⟩
  · intro tile
    have hbound := normalizeCounts_le_four hvalid.2.2.1 tile
    have htotal : normalizeCounts (totalCounts input) tile =
        ((normalizedHand input hvalid.1).counts tile : Int) +
          ((Capacity.fixedTiles (parsedMelds input hparsed)).count tile : Int) := by
      rw [normalizedHand_counts_cast hvalid.1, parsedMelds_counts hparsed]
      exact normalizeCounts_add _ _ tile
    rw [htotal] at hbound
    omega
  · have hcount := normalizedHand_tileCount hvalid.1
    have hsize := hvalid.2.2.2.2.1
    rw [hlength]
    rcases hsize with h13 | h14
    · left
      omega
    · right
      omega

theorem validated_overall_eq_some_iff
    (hresult : validateAndNormalize input = .ok normalized) :
    Capacity.overallMinimumSearch normalized.fixed normalized.hand = some value ↔
      Capacity.IsOverallShanten normalized.fixed normalized.hand value :=
  Capacity.overallMinimumSearch_eq_some_iff
    (validateAndNormalize_valid hresult).1 (validateAndNormalize_valid hresult).2

theorem validated_overall_exists_unique
    (hresult : validateAndNormalize input = .ok normalized) :
    ∃! value : Int,
      Capacity.overallMinimumSearch normalized.fixed normalized.hand = some value ∧
        Capacity.IsOverallShanten normalized.fixed normalized.hand value :=
  Capacity.overallMinimumSearch_exists_unique
    (validateAndNormalize_valid hresult).1 (validateAndNormalize_valid hresult).2

/-- Red identity may vary, but fixed-meld kinds and normalized tile contents may not. -/
def Equivalent (left right : Input) : Prop :=
  normalizeCounts left.standing = normalizeCounts right.standing ∧
    left.melds.map (fun raw => (raw.kind, normalizeCounts raw.tiles)) =
      right.melds.map (fun raw => (raw.kind, normalizeCounts raw.tiles))

lemma parseMeld_congr
    (hkind : left.kind = right.kind)
    (hcounts : normalizeCounts left.tiles = normalizeCounts right.tiles) :
    parseMeld left = parseMeld right := by
  unfold parseMeld
  congr 1
  funext target
  simp only [MatchesMeld, hkind, hcounts]

private lemma parseMelds_congr {left right : List MeldInput}
    (heq : left.map (fun raw => (raw.kind, normalizeCounts raw.tiles)) =
      right.map (fun raw => (raw.kind, normalizeCounts raw.tiles))) :
    left.map parseMeld = right.map parseMeld := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons raw rest => simp at heq
  | cons raw rest ih =>
      cases right with
      | nil => simp at heq
      | cons other others =>
          simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at heq
          simp only [List.map_cons]
          exact congrArg₂ List.cons (parseMeld_congr heq.1.1 heq.1.2) (ih heq.2)

theorem normalized_equivalent
    (hleft : validateAndNormalize left = .ok normalizedLeft)
    (hright : validateAndNormalize right = .ok normalizedRight)
    (heq : Equivalent left right) :
    normalizedLeft.fixed = normalizedRight.fixed ∧
      normalizedLeft.hand = normalizedRight.hand := by
  obtain ⟨hlvalid, hl, rfl⟩ := validateAndNormalize_ok_iff.mp hleft
  obtain ⟨hrvalid, hr, rfl⟩ := validateAndNormalize_ok_iff.mp hright
  change parsedMelds left hl = parsedMelds right hr ∧
    normalizedHand left hlvalid.1 = normalizedHand right hrvalid.1
  have hlength : left.melds.length = right.melds.length := by
    have := congrArg List.length heq.2
    simpa using this
  have hparsed : left.melds.map parseMeld = right.melds.map parseMeld := by
    exact parseMelds_congr heq.2
  have hfixed : parsedMelds left hl = parsedMelds right hr := by
    apply (List.map_inj_right (f := some) (fun _ _ h => Option.some.inj h)).mp
    have hsome (input : Input) (h : ∀ index : Fin input.melds.length,
        (parseMeld input.melds[index]).isSome = true) :
        (parsedMelds input h).map some = input.melds.map parseMeld := by
      simp only [parsedMelds, List.map_ofFn]
      calc
        _ = List.ofFn (fun index : Fin input.melds.length => parseMeld input.melds[index]) := by
          congr 1
          funext index
          exact Option.some_get (h index)
        _ = _ := by
          change List.ofFn (parseMeld ∘ input.melds.get) = _
          rw [← List.map_ofFn, List.ofFn_get]
    rw [hsome left hl, hsome right hr, hparsed]
  refine ⟨hfixed, ?_⟩
  unfold normalizedHand
  apply congrArg₂ Hand.mk
  · funext tile
    calc
      (MahjongDomain.aggregateInt37 (fun index => left.standing index)
        (DomainAdapter.toDomainTile tile)).toNat =
          (normalizeCounts left.standing tile).toNat := by
            rw [← DomainAdapter.normalizeCounts_matches_domain]
      _ = (normalizeCounts right.standing tile).toNat :=
        congrArg Int.toNat (congrFun heq.1 tile)
      _ = (MahjongDomain.aggregateInt37 (fun index => right.standing index)
          (DomainAdapter.toDomainTile tile)).toNat := by
            rw [DomainAdapter.normalizeCounts_matches_domain]
  · exact hlength

theorem overall_normalization_invariant
    (hleft : validateAndNormalize left = .ok normalizedLeft)
    (hright : validateAndNormalize right = .ok normalizedRight)
    (heq : Equivalent left right) :
    Capacity.overallMinimumSearch normalizedLeft.fixed normalizedLeft.hand =
      Capacity.overallMinimumSearch normalizedRight.fixed normalizedRight.hand := by
  obtain ⟨hfixed, hhand⟩ := normalized_equivalent hleft hright heq
  rw [hfixed, hhand]

end Shanten.Input37
