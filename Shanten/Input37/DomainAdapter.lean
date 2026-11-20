import Shanten.DomainAdapter
import Shanten.Input37.Basic
import Mathlib.Tactic.FinCases

namespace Shanten.DomainAdapter

theorem normalizeTile_matches_domain (index : Fin 37) :
    toDomainTile (Shanten.Input37.normalizeTile index) =
      MahjongDomain.Int37Index.tile index := by
  simp [Shanten.Input37.normalizeTile,
    Shanten.DomainAdapter.toDomainTile_ofDomainTile]

theorem capacity_matches_domain (index : Fin 37) :
    Shanten.Input37.capacity index = MahjongDomain.Int37Index.capacity index := by
  rfl

theorem normalIndex_matches_domain (tile : Shanten.Tile) :
    Shanten.Input37.normalIndex tile =
      (toDomainTile tile).int37Index := by
  rfl

theorem normalizeCounts_matches_domain
    (counts : Shanten.Input37.Counts37) (tile : Shanten.Tile) :
    Shanten.Input37.normalizeCounts counts tile =
      MahjongDomain.aggregateInt37 (fun index => counts index) (toDomainTile tile) := by
  rfl

end Shanten.DomainAdapter
