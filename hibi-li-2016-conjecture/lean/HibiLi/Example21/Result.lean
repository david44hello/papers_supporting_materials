/-
HibiLi/Example21/Result.lean — exact geometric f-vectors in Example 2.1.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Example21.OrderData
import HibiLi.Example21.ChainData
import HibiLi.Example21.Catalog
import HibiLi.Example21.FiniteCounts

namespace HibiLi
namespace Example21

theorem order_realPoints_eq : realPoints OrderData.points = orderVertex := by
  ext idx row
  fin_cases idx <;> cases row <;>
    norm_num [realPoints, OrderData.points, OrderData.qVec, orderVertex, xVec]

theorem chain_realPoints_eq : realPoints ChainData.points = chainVertex := by
  ext idx row
  fin_cases idx <;> cases row <;>
    norm_num [realPoints, ChainData.points, ChainData.qVec, chainVertex, xVec]

theorem order_fNum_eq_count (dim : ℕ) :
    fNum (orderPolytope XElem) dim = (OrderData.countedMasks dim).card := by
  rw [orderPolytope_X_eq_convexHull, ← order_realPoints_eq]
  apply fNum_eq_catalog_card (exclusion := OrderData.nonfaceCert)
  intro mask
  have hh := OrderData.certificates_valid mask
  cases hc : OrderData.faceCert mask <;>
    simpa only [OrderData.CertificateValid, hc] using hh

theorem chain_fNum_eq_count (dim : ℕ) :
    fNum (chainPolytope XElem) dim = (ChainData.countedMasks dim).card := by
  rw [chainPolytope_X_eq_convexHull, ← chain_realPoints_eq]
  apply fNum_eq_catalog_card (exclusion := ChainData.nonfaceCert)
  intro mask
  have hh := ChainData.certificates_valid mask
  cases hc : ChainData.faceCert mask <;>
    simpa only [ChainData.CertificateValid, hc] using hh

end Example21

theorem ex_2_1_proved (k : ℕ) :
    fNum (orderPolytope XElem) k = [8, 24, 34, 24, 8, 1].getD k 0 ∧
    fNum (chainPolytope XElem) k = [8, 24, 35, 26, 9, 1].getD k 0 := by
  by_cases hk : k < 6
  · rw [Example21.order_fNum_eq_count, Example21.chain_fNum_eq_count]
    interval_cases k <;>
      norm_num [Example21.OrderData.count_0, Example21.OrderData.count_1,
        Example21.OrderData.count_2, Example21.OrderData.count_3,
        Example21.OrderData.count_4, Example21.OrderData.count_5,
        Example21.ChainData.count_0, Example21.ChainData.count_1,
        Example21.ChainData.count_2, Example21.ChainData.count_3,
        Example21.ChainData.count_4, Example21.ChainData.count_5]
  · have hk6 : 6 ≤ k := Nat.le_of_not_gt hk
    rw [Example21.orderPolytope_X_fNum_zero hk6, Example21.chainPolytope_X_fNum_zero hk6]
    simp [hk6]

end HibiLi
