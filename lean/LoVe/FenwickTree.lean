import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Find
import Aesop

namespace FenwickTree

theorem Nat.land_with_succ_le' (idx: Nat): (Nat.land (idx + 1) idx) ≤ idx := by
       unfold Nat.land
       unfold Nat.bitwise
       induction idx with
       | zero => simp
       | succ n' ih =>
            simp [Nat.succ_ne_zero] at *
            sorry

axiom Nat.land_with_succ_le (idx: Nat): (Nat.land (idx + 1) idx) ≤ idx
--
-- A more general statement is a && b <= min(a,b)

axiom Nat.lor_with_succ_gt (idx: Nat): (Nat.lor idx ( idx + 1)) > idx


-- Reference: https://cp-algorithms.com/data_structures/fenwick.html

-- structure Fenwick (n: Nat) where
--     arr: Vector Nat n
--     deriving Inhabited, Repr

def prefixSumIncl (vec: Array Nat) (till: Nat) (h: till < vec.size): Nat :=
    let rec sum i acc (h': i<=till) :=
        if iEq0: i == 0  then acc + (vec.get i (by omega))
        else (
            let acc' := acc + vec.get i (by omega)
            let i' :=  i - 1
            have iGt0 : i > 0 := by
                 cases i <;> simp [*] at *
            have iMinus1LtI : i > i' := by
                 cases i
                 · assumption
                 · unfold i' ; simp
            sum i' acc' (by omega)
        )
        termination_by i
    sum till 0 (by simp)

-- #eval prefixSumIncl #[1,2,3,4] 2 (by simp)
    
private def g (i: Nat) :=
    i.land (i+1)

/-- Represents a Fenwick Tree over an array of values -/
structure Fenwick where
  size : Nat
  tree : Array Nat
  size_valid : tree.size = size
  deriving Repr


def Fenwick.mkWith0 (len: Nat := 0):  Fenwick :=
    {
        size:= len
        tree:= Array.mkArray ( len ) 0
        size_valid := (by simp)
    }

#find ?x < ?y -> ?z - ?y < ?z - ?x

def Fenwick.pointIncrease (fen: Fenwick)
    (idx: Nat)
    (increaseBy: Nat)
    (idxValid: idx < fen.size) : Fenwick :=
        have ⟨size,tree,valid_size⟩ := fen
        let curVal := tree.get idx (by simp [*] at *)
        let newIdx := idx.lor (idx+1)
        have newIdxIncreases : newIdx > idx := by
            unfold newIdx
            have h := Nat.lor_with_succ_gt idx
            exact h
             
        let updatedFen := (
            if newIdxValid : newIdx >= fen.size then fen
            else
                have idxWrtFenSizeDecreasing : fen.size - newIdx < fen.size - idx := by
                    simp [*] at *
                    apply Nat.sub_lt_sub_left
                    · exact (Nat.lt_trans newIdxIncreases newIdxValid) 
                    · exact newIdxIncreases
                fen.pointIncrease newIdx increaseBy (by
                    simp [*] at *
                    exact newIdxValid
                )) 
        {
        size:=size
        tree:=(updatedFen.tree.set idx (curVal + increaseBy) (by
                        sorry
                ))
        size_valid:=(by
            sorry
            -- simp [*] at *
        )
        }
    termination_by (sorry)
    -- termination_by (fen.size - idx)

#eval Nat.land 3 4  -- = 0
#eval Nat.land 7 8  -- = 0
#eval Nat.land 12 13  -- = 12

#find ?a <= ?b -> ?a - 1 < ?b

#find ¬ _ -> 0 < ?x

theorem Nat.not_zero_implies_atleast_1 : ∀ (n : Nat), (h: ¬ (n = 0)) -> n >= 1 :=
    by
     intro n h
     cases n <;> simp [*] at *
     

def Fenwick.prefixSum (fen: Fenwick) (idx: Nat) (h: idx < fen.size)  : Nat :=
    let valAtIdx := fen.tree.get idx (by
        have ⟨size,arr,size_valid⟩ := fen
        simp [*] at *
    )
    if idxEq0 : idx = 0 then
       valAtIdx
    else (
        let idx' := idx &&& (idx + 1)
        if idx'Eq0: idx' = 0 then valAtIdx
        else (
            have idx'Atleast1 : idx' >= 1 :=
                 Nat.not_zero_implies_atleast_1 idx' idx'Eq0
            have idx'LtIdx : idx' <= idx := by
                 have h' := Nat.land_with_succ_le idx
                 unfold idx'
                 rw [Nat.and_comm]
                 assumption
            have idx'_minus_1_lt_idx : idx' - 1 < idx := by
                 omega
            valAtIdx + (fen.prefixSum ( idx' - 1) (by
                unfold idx'
                simp [*]  at *
                omega
            )))
    )
     termination_by idx


-- TODO: 
 def Fenwick.rangeQuery {n: Nat} (fen: Fenwick) (l: Nat) (r: Nat)  : Nat :=
     _


section Tmp
def fen' : Fenwick := Fenwick.mkWith0 5

-- #eval! (((((fen'.pointIncrease 0 1 (by sorry)).pointIncrease 1 2 (by sorry)).pointIncrease 2 3 (by sorry)).pointIncrease 3 4 (by sorry)).pointIncrease 4 5 (by sorry)).prefixSum 4 (by sorry)


end Tmp

section Tmp
def fen: Fenwick :=
    {
        size:= 5
        tree:= #[1,2,3,4,5]
        size_valid:= (by simp)
    }

#eval Fenwick.prefixSum fen 0 (by unfold fen; simp)
#eval Fenwick.prefixSum fen 1 (by unfold fen; simp)
#eval Fenwick.prefixSum fen 2 (by
        unfold fen
        simp
      )
#eval Fenwick.prefixSum fen 3 (by
        unfold fen
        simp
      )
#eval Fenwick.prefixSum fen 4 (by
        unfold fen
        simp
      )

end Tmp

end FenwickTree
