import Shanten.DomainAdapter
import Shanten.Input37.Basic
import Mathlib.Tactic.FinCases

namespace Shanten.DomainAdapter

theorem normalizeTile_matches_domain (index : Fin 37) :
    toDomainTile (Shanten.Input37.normalizeTile index) =
      MahjongDomain.Int37Index.tile index := by
  fin_cases index <;> decide

theorem capacity_matches_domain (index : Fin 37) :
    Shanten.Input37.capacity index = MahjongDomain.Int37Index.capacity index := by
  fin_cases index <;> decide

theorem normalizeCounts_matches_domain
    (counts : Shanten.Input37.Counts37) (tile : Shanten.Tile) :
    Shanten.Input37.normalizeCounts counts tile =
      MahjongDomain.aggregateInt37 (fun index => counts index) (toDomainTile tile) := by
  simp only [Shanten.Input37.normalizeCounts, MahjongDomain.aggregateInt37]
  apply Finset.sum_congr rfl
  intro index _
  by_cases h : Shanten.Input37.normalizeTile index = tile
  · have h' : toDomainTile tile = MahjongDomain.Int37Index.tile index := by
      rw [← normalizeTile_matches_domain index]
      exact (congrArg toDomainTile h).symm
    simp [h, h']
  · have h' : toDomainTile tile ≠ MahjongDomain.Int37Index.tile index := by
      intro h'
      apply h
      apply toDomainTile_injective
      rw [normalizeTile_matches_domain index]
      exact h'.symm
    simp [h, h']

end Shanten.DomainAdapter
