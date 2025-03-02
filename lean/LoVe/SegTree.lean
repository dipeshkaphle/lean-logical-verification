import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Find
import Aesop

namespace SegmentTree

-- Reference: https://cp-algorithms.com/data_structures/segment_tree.html#implementation

structure Range where
  l : Nat
  r: Nat
  lLeR : l <= r

def Range.contains (x: Nat) (range: Range) :Bool :=
    x >= range.l ∧ x <= range.r

-- Split the range such that they are definitely disjoint and valid
def Range.splitAt (rng: Range) (at': Nat) : Option Range × Option Range :=
    let ⟨ l', r', _ ⟩ := rng
    let m' := Nat.min r' at'
    let m'' := Nat.max l' (at' + 1)
    let fstRange := if h: l' <= m' then Option.some (Range.mk l' m' h ) else .none
    let sndRange := if h: m'' <= r' then Option.some (Range.mk m'' r' h) else .none
    ( fstRange, sndRange )

def mid (l r : Nat) :=
    Nat.div2 (l+r)


theorem lPlusRAtleast2l : (h: l <= r) -> l <= (l + r) / 2 := by
        omega

theorem lrMidLtR (h: l <= r) (h': ¬ (l = r)) : mid l r < r := by
    have h'' := Nat.lt_of_le_of_ne h h'
    unfold mid
    rw [Nat.div2_val]
    omega

theorem lLeMidLR : (h: l <= r) -> l <= mid l r := by
    intro h
    unfold mid
    rw [Nat.div2_val]
    apply lPlusRAtleast2l
    assumption


inductive SegTree : Range -> Type where
    | leaf l {r} {h: l = r} (val: Int) : SegTree (Range.mk l r (by omega))
    | node l r lLeR (lNeR: ¬ l = r) (val: Int) (left: SegTree (Range.mk l (mid l r) (by
      exact lLeMidLR lLeR
    ))) (right: SegTree (Range.mk (Nat.min r ((mid l r) + 1 )) r (by
        unfold Nat.min
        apply Nat.min_le_left
    ) )) : SegTree (Range.mk l r lLeR)

def SegTree.sum (seg: SegTree rng) (desiredRange: Range) : Int :=
    match seg with
    | .leaf l v => if desiredRange.contains l then v else 0
    | .node l r lLeR _ v leftSubtree rightSubtree =>
        let ⟨a,b, _⟩ := desiredRange
        if desiredRange.contains l ∧ desiredRange.contains r then 
          v
        else if r < a || l > b then 
          0
        else
          let m := Nat.div2 (l+r)
          let ⟨lRange,rRange⟩ := desiredRange.splitAt m
          ( match lRange, rRange with
          | Option.some leftRange, Option.some rightRange => sum leftSubtree leftRange  + sum rightSubtree rightRange
          | Option.some leftRange , Option.none => sum leftSubtree leftRange
          | Option.none , Option.some rightRange=> sum rightSubtree rightRange
          | Option.none , Option.none => 0 )

def SegTree.pointQuery (seg: SegTree rng) (idx:Nat) :=
    seg.sum (Range.mk idx idx (by simp))

private def SegTree.getVal (seg:SegTree rng) :=
    match seg with
    | .leaf _ v => v
    | .node _ _ _ _ v _ _ => v


def SegTree.invariant (seg: SegTree rng) : Prop :=
  match seg with
  | .leaf _ val => True  -- Leaf nodes maintain no special property
  | .node _ _ _ _ val left right => 
      val = SegTree.getVal left + SegTree.getVal right ∧
      SegTree.invariant left ∧ SegTree.invariant right

def SegTree.update {rng: Range} (seg: SegTree rng) (idx: Nat) (newVal: Int) : SegTree rng :=
    match seg with
    | @SegTree.leaf l r h v => if l = idx then @SegTree.leaf l r h newVal else @SegTree.leaf l r h v
    | .node l r lLeR lNeR v leftSubtree rightSubtree =>
        if l <= idx && idx <= r then
          let m := mid l r
          if idx <= m then
            let newLeft := update leftSubtree idx newVal
            let newVal := getVal (newLeft) + getVal rightSubtree
            .node l r lLeR lNeR newVal newLeft rightSubtree
          else
            let newRight := update rightSubtree idx newVal
            let newVal := getVal leftSubtree + getVal newRight
            .node l r lLeR lNeR newVal leftSubtree newRight
        else
          -- Index outside of current range, no update needed
          .node l r lLeR lNeR v leftSubtree rightSubtree


#find ?a <= ?b -> ¬ ?a = ?b -> ?a < ?b
#find ?a > ?b -> ?c - ?a < ?c - ?b

private def mkWith0' (l: Nat) (r: Nat) (h: l <= r) : SegTree (Range.mk l r h) :=
    if h': l = r then (@SegTree.leaf l r h' 0)
    else (
            have lPlusRDecreases : mid l r < r := by
                 exact (lrMidLtR h h')
                 
            have midLRPlus1LeR : mid l r + 1 <= r := by
                 rw [Nat.succ_le_iff]
                 exact lPlusRDecreases

            have terminationCond : r - r.min (mid l r + 1) < r - l := by
                 have h''' := lLeMidLR h
                 apply Nat.sub_lt_sub_left
                 · omega 
                 · unfold mid at *
                   rw [Nat.div2_val] at *
                   unfold Nat.min
                   rw [Nat.min_def]
                   by_cases h'' : r <= ( (l+r) / 2 + 1 )
                   { simp [h''] ; omega }
                   { simp [h''] ; omega }

            let left := mkWith0' l (mid l r) ( by
                exact (lLeMidLR h)
            )
            let right := mkWith0' (r.min ((mid l r) +1)) r (by
                unfold mid at *
                rw [Nat.div2_val] at *
                unfold Nat.min
                rw [Nat.min_def]
                by_cases h'' : r <= ( (l+r) / 2 + 1 )
                { simp [h''] }
                { simp [h'']; omega }
            )
            .node l r h h' 0 left right
    )
    termination_by r - l

def SegTree.mkWith0 (len: Nat) : SegTree (Range.mk 0 len (by simp)) :=
    mkWith0' 0 len (by simp)

def SegTree.toArray (seg: SegTree rng) : Array Int :=
  match rng with
  | Range.mk l r _ =>
      let size := r - l + 1
      let arr := mkArray size 0
      (List.range size).foldl (fun a i => 
        a.set! i (SegTree.pointQuery seg (i+l))) arr


section Example
  -- Generated by sir Claude
  --
  --
  -- Manually construct a segment tree for array [1, 3, 5, 7, 9]
  -- Structure will be:
  --                  [0-4] (sum: 25)
  --                 /          \
  --        [0-2] (sum: 9)     [3-4] (sum: 16)
  --        /         \        /       \
  --  [0-1] (sum: 4)  [2] (5) [3] (7)  [4] (9)
  --  /      \
  -- [0](1)  [1](3)
  
  -- Leaf nodes for indices 0 to 4
  def leaf0 : SegTree (Range.mk 0 0 (by simp)) := @SegTree.leaf 0 0 (by rfl) 1
  def leaf1 : SegTree (Range.mk 1 1 (by simp)) := @SegTree.leaf 1 1 (by rfl) 3
  def leaf2 : SegTree (Range.mk 2 2 (by simp)) := @SegTree.leaf 2 2 (by rfl) 5
  def leaf3 : SegTree (Range.mk 3 3 (by simp)) := @SegTree.leaf 3 3 (by rfl) 7
  def leaf4 : SegTree (Range.mk 4 4 (by simp)) := @SegTree.leaf 4 4 (by rfl) 9
  
  -- Internal node for indices 0 and 1 (sum = 4)
  def node01 : SegTree (Range.mk 0 1 (by simp)) := 
    SegTree.node 0 1 (by simp) (by simp) 4 leaf0 leaf1
  
  -- Internal node for indices 3 and 4 (sum = 16)
  def node34 : SegTree (Range.mk 3 4 (by simp)) := 
    SegTree.node 3 4 (by simp) (by simp) 16 leaf3 leaf4
  
  -- Internal node for indices 0, 1, and 2 (sum = 9)
  def node02 : SegTree (Range.mk 0 2 (by simp)) := 
    SegTree.node 0 2 (by simp) (by simp)  9 node01 leaf2
  
  -- Root node 
  def exampleTree : SegTree (Range.mk 0 4 (by simp)) := 
    SegTree.node 0 4 (by simp) (by simp) 25 node02 node34

  #eval SegTree.sum node34 (Range.mk 0 2 (by simp)) -- nothing since it's out of range
  #eval SegTree.toArray exampleTree

  #eval SegTree.sum exampleTree (Range.mk 0 2 (by simp))   -- Sum of [1, 3, 5] = 9
  #eval SegTree.sum exampleTree (Range.mk 1 3 (by simp))   -- Sum of [3, 5, 7] = 15
  #eval SegTree.sum exampleTree (Range.mk 0 4 (by simp))   -- Entire array sum= 25
  #eval SegTree.sum exampleTree (Range.mk 0 0 (by simp))   -- Single element = 1
  #eval SegTree.sum exampleTree (Range.mk 1 1 (by simp))   -- Single element = 3
  #eval SegTree.sum exampleTree (Range.mk 2 2 (by simp))   -- Single element = 5
  #eval SegTree.sum exampleTree (Range.mk 3 3 (by simp))   -- Single element = 7
  #eval SegTree.sum exampleTree (Range.mk 4 4 (by simp))   -- Single element = 9
  
  
  def updatedTree1 := SegTree.update exampleTree 2 10  -- => [1,3,10,7,9]
  #eval SegTree.toArray updatedTree1
  
  #eval SegTree.sum updatedTree1 (Range.mk 0 2 (by simp))   -- 14
  #eval SegTree.sum updatedTree1 (Range.mk 0 4 (by simp))   -- 30
  
  def updatedTree2 := SegTree.update updatedTree1 0 5   -- => [5,3,10,7,9]
  def updatedTree3 := SegTree.update updatedTree2 4 15  -- => [5,3,10,7,15]

  #eval SegTree.toArray updatedTree3
  #eval SegTree.sum updatedTree3 (Range.mk 0 4 (by simp))   -- 40
  #eval SegTree.sum updatedTree3 (Range.mk 3 4 (by simp))   -- sum( [7, 15] ) = 22
  #eval SegTree.sum updatedTree3 (Range.mk 0 0 (by simp))   -- 5
  #eval SegTree.sum updatedTree3 (Range.mk 4 4 (by simp))   -- 15

end Example


inductive SegArrEquivalence : (arr: Array Int) -> (SegTree (Range.mk 0 arr.size (by simp))) -> Prop where
    | intro (len: Nat) : SegArrEquivalence (Array.mkArray len 0) (SegTree.mkWith0 (Array.mkArray len 0).size)
    -- | eqv_with_set : _
    -- | eqv_with_get : _

end SegmentTree
