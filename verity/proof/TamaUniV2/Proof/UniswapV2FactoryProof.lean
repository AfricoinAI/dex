import TamaUniV2.Spec.UniswapV2FactorySpec

namespace TamaUniV2.Proof.UniswapV2FactoryProof

open Verity
open Verity.EVM.Uint256
open TamaUniV2.Spec.UniswapV2FactorySpec
open TamaUniV2.UniswapV2Factory

attribute [local simp] getPair allPairs allPairsLength pairForSlot allPairsSlot allPairsLengthSlot
  UniswapV2FactoryBase.getPair UniswapV2FactoryBase.allPairs
  UniswapV2FactoryBase.allPairsLength

-- tama: discharges=factory_getPair_spec
theorem getPair_meets_spec (tokenA tokenB : Address) (s : ContractState) :
  factory_getPair_spec tokenA tokenB ((getPair tokenA tokenB).run s).fst s := by
  rfl

-- tama: discharges=factory_allPairsLength_spec
theorem allPairsLength_meets_spec (s : ContractState) :
  factory_allPairsLength_spec ((allPairsLength).run s).fst s := by
  rfl

-- tama: discharges=factory_allPairs_success_spec
theorem allPairs_meets_spec (index : Uint256) (s : ContractState) :
  factory_allPairs_success_spec index ((allPairs index).run s).fst s := by
  intro h
  have hval : index.val < (s.storage allPairsLengthSlot.slot).val := h
  simp [allPairs, UniswapV2FactoryBase.allPairs,
    Verity.getStorage, Verity.getMappingUint, Verity.require, Contract.run,
    ContractResult.fst, Verity.bind, Bind.bind, Verity.pure, Pure.pure, hval]

end TamaUniV2.Proof.UniswapV2FactoryProof
