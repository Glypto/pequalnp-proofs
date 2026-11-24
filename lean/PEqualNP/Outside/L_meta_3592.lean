import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3592

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The value of a gate on a list of wire values, one evaluation step, and a run of gates.
def gv (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [gv g w]

def run (G : List Gate) (w : List Bool) : List Bool :=
  G.foldl step w

theorem run_cons (g : Gate) (G : List Gate) (w : List Bool) :
    run (g :: G) w = run G (step w g) := rfl

theorem run_append (G1 G2 : List Gate) (w : List Bool) :
    run (G1 ++ G2) w = run G2 (run G1 w) := by
  simp [run, List.foldl_append]

theorem run_length (G : List Gate) (w : List Bool) :
    (run G w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp [run]
  | cons g G ih =>
    rw [run_cons, ih]
    simp [step]
    omega

-- Reading a list of wire values, before and after one position is taken out.
theorem getD_append_lt (W : List Bool) (z : Bool) (i : ℕ) (h : i < W.length) :
    (W ++ [z]).getD i false = W.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_len (W : List Bool) (z : Bool) :
    (W ++ [z]).getD W.length false = z := by
  simp [List.getD_eq_getElem?_getD]

theorem eraseIdx_append_len (W : List Bool) (z : Bool) :
    (W ++ [z]).eraseIdx W.length = W := by
  rw [List.eraseIdx_append_of_length_le (le_refl _)]
  simp

theorem getD_erase_lt (W : List Bool) (r w : ℕ) (h : w < r) :
    (W.eraseIdx r).getD w false = W.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx, h]

theorem getD_erase_gt (W : List Bool) (r w : ℕ) (h : r < w) :
    (W.eraseIdx r).getD (w - 1) false = W.getD w false := by
  have h1 : ¬ (w - 1 < r) := by omega
  have h2 : w - 1 + 1 = w := by omega
  simp [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx, h1, h2]

theorem getD_erase_big (W : List Bool) (r t : ℕ) (h : W.length ≤ t) :
    (W.eraseIdx r).getD t false = false := by
  apply List.getD_eq_default
  exact le_trans (List.length_eraseIdx_le _ _) h

theorem run_getD_lt (G : List Gate) (W : List Bool) (i : ℕ) (h : i < W.length) :
    (run G W).getD i false = W.getD i false := by
  induction G generalizing W with
  | nil => rfl
  | cons g G ih =>
    rw [run_cons, ih (step W g) (by simp [step]; omega)]
    exact getD_append_lt W _ i h

-- The simulation: a run of rewritten gates on the wires with position r taken out
-- gives the original run with position r taken out.
theorem sim (r : ℕ) (τ : Gate → Gate) (Inv : ℕ → List Bool → Prop) (Good : Gate → Prop)
    (hlen : ∀ k W, Inv k W → r < W.length)
    (hstep : ∀ k W z, Inv (k + 1) W → Inv k (W ++ [z]))
    (hgl : ∀ k W h, Inv (k + 1) W → Good h → gv (τ h) (W.eraseIdx r) = gv h W) :
    ∀ (G : List Gate) (W : List Bool), Inv G.length W → (∀ h ∈ G, Good h) →
      run (G.map τ) (W.eraseIdx r) = (run G W).eraseIdx r ∧ Inv 0 (run G W) := by
  intro G
  induction G with
  | nil =>
    intro W hW _
    exact ⟨rfl, hW⟩
  | cons h G ih =>
    intro W hW hG
    have hW' : Inv (G.length + 1) W := hW
    have h1 : gv (τ h) (W.eraseIdx r) = gv h W := hgl _ W h hW' (hG h (by simp))
    have h2 := ih (W ++ [gv h W]) (hstep _ W _ hW') (fun h' hh' => hG h' (by simp [hh']))
    have hr : r < W.length := hlen _ W hW'
    have h3 : (W ++ [gv h W]).eraseIdx r = W.eraseIdx r ++ [gv h W] :=
      List.eraseIdx_append_of_lt_length hr _
    constructor
    · show run (τ h :: G.map τ) (W.eraseIdx r) = (run (h :: G) W).eraseIdx r
      rw [run_cons, run_cons]
      have h4 : step (W.eraseIdx r) (τ h) = (step W h).eraseIdx r := by
        show W.eraseIdx r ++ [gv (τ h) (W.eraseIdx r)] = (W ++ [gv h W]).eraseIdx r
        rw [h3, h1]
      rw [h4]
      exact h2.1
    · exact h2.2

-- Renaming of wire indices when position r is taken out and read as position t.
def rho (r t w : ℕ) : ℕ :=
  if w < r then w else if w = r then t else w - 1

def ren (r t : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (rho r t)⟩

theorem rho_spec (r t : ℕ) (W : List Bool)
    (ht : (W.eraseIdx r).getD t false = W.getD r false) (w : ℕ) :
    (W.eraseIdx r).getD (rho r t w) false = W.getD w false := by
  unfold rho
  split_ifs with h1 h2
  · exact getD_erase_lt W r w h1
  · subst h2
    exact ht
  · exact getD_erase_gt W r w (by omega)

theorem gv_ren (r t : ℕ) (W : List Bool) (g : Gate)
    (ht : (W.eraseIdx r).getD t false = W.getD r false) :
    gv (ren r t g) (W.eraseIdx r) = gv g W := by
  have hmap : (g.inputs.map (rho r t)).map (fun i => (W.eraseIdx r).getD i false)
      = g.inputs.map (fun i => W.getD i false) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro w _
    exact rho_spec r t W ht w
  show g.op.eval ((g.inputs.map (rho r t)).map fun i => (W.eraseIdx r).getD i false)
    = g.op.eval (g.inputs.map fun i => W.getD i false)
  rw [hmap]

def GoodF (h : Gate) : Prop :=
  h.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ h.inputs.length ≤ 2

theorem ren_fan (r t : ℕ) (h : Gate) (hh : GoodF h) :
    (ren r t h).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (ren r t h).inputs.length ≤ 2 := by
  simpa [ren, GoodF] using hh

-- Rewriting of a gate when the wire at position r is always true and is taken out.
def shift (r w : ℕ) : ℕ :=
  if w < r then w else w - 1

def elimT (r : ℕ) : Gate → Gate
  | ⟨GateOp.and, ins⟩ => ⟨GateOp.and, (ins.filter (fun w => decide (w ≠ r))).map (shift r)⟩
  | ⟨GateOp.or, ins⟩ => if r ∈ ins then ⟨GateOp.and, []⟩ else ⟨GateOp.or, ins.map (shift r)⟩
  | ⟨GateOp.not, ins⟩ =>
    if ins.head? = some r then ⟨GateOp.or, []⟩ else ⟨GateOp.not, ins.map (shift r)⟩
  | g => g

theorem shift_spec (r : ℕ) (W : List Bool) (w : ℕ) (hw : w ≠ r) :
    (W.eraseIdx r).getD (shift r w) false = W.getD w false := by
  unfold shift
  split_ifs with h1
  · exact getD_erase_lt W r w h1
  · exact getD_erase_gt W r w (by omega)

theorem all_elim (r : ℕ) (W : List Bool) (hr : W.getD r false = true) (ins : List ℕ) :
    (((ins.filter (fun w => decide (w ≠ r))).map (shift r)).map
      (fun i => (W.eraseIdx r).getD i false)).all id
      = (ins.map (fun i => W.getD i false)).all id := by
  induction ins with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : a = r
    · subst ha
      simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
        ite_false, List.map_cons, List.all_cons, hr, id, Bool.true_and]
      exact ih
    · have hd : decide (a ≠ r) = true := by simpa using ha
      simp only [List.filter_cons, hd, ite_true, List.map_cons, List.all_cons, id,
        shift_spec r W a ha]
      rw [ih]

theorem gv_elimT (r : ℕ) (W : List Bool) (h : Gate) (hr : W.getD r false = true)
    (hop : h.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hn : h.op = GateOp.not → h.inputs.length ≤ 1) :
    gv (elimT r h) (W.eraseIdx r) = gv h W := by
  rcases h with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · exact all_elim r W hr ins
  · by_cases hm : r ∈ ins
    · have h1 : gv ⟨GateOp.or, ins⟩ W = true := by
        show (ins.map (fun i => W.getD i false)).any id = true
        rw [List.any_eq_true]
        exact ⟨true, List.mem_map.mpr ⟨r, hm, hr⟩, rfl⟩
      rw [h1]
      simp [elimT, hm, gv, GateOp.eval]
    · have hmap : (ins.map (shift r)).map (fun i => (W.eraseIdx r).getD i false)
          = ins.map (fun i => W.getD i false) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro w hw
        have hne : w ≠ r := fun e => hm (e ▸ hw)
        exact shift_spec r W w hne
      have h1 : elimT r ⟨GateOp.or, ins⟩ = ⟨GateOp.or, ins.map (shift r)⟩ := by
        simp [elimT, hm]
      rw [h1]
      show ((ins.map (shift r)).map fun i => (W.eraseIdx r).getD i false).any id
        = (ins.map fun i => W.getD i false).any id
      rw [hmap]
  · have hl : ins.length ≤ 1 := hn rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [elimT, gv, GateOp.eval]
    · by_cases ha : a = r
      · subst ha
        have h1 : gv ⟨GateOp.not, [a]⟩ W = false := by
          show (!(W.getD a false)) = false
          rw [hr]
          rfl
        rw [h1]
        simp [elimT, gv, GateOp.eval]
      · have h1 : elimT r ⟨GateOp.not, [a]⟩ = ⟨GateOp.not, [shift r a]⟩ := by
          simp [elimT, ha]
        rw [h1]
        show (!([(W.eraseIdx r).getD (shift r a) false].headD false))
          = (!([W.getD a false].headD false))
        rw [shift_spec r W a ha]
    · simp only [List.length_cons] at hl
      omega

theorem elimT_fan (r : ℕ) (h : Gate)
    (hop : h.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hl : h.inputs.length ≤ 2) :
    (elimT r h).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (elimT r h).inputs.length ≤ 2 := by
  rcases h with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have hl' : ins.length ≤ 2 := hl
  rcases hop with rfl | rfl | rfl
  · refine ⟨by simp [elimT], ?_⟩
    have h1 : (elimT r ⟨GateOp.and, ins⟩).inputs
        = (ins.filter (fun w => decide (w ≠ r))).map (shift r) := rfl
    rw [h1, List.length_map]
    exact le_trans (List.length_filter_le _ _) hl'
  · by_cases hm : r ∈ ins
    · simp [elimT, hm]
    · simp [elimT, hm, hl']
  · by_cases hm : ins.head? = some r
    · simp [elimT, hm]
    · simp [elimT, hm, hl']

-- The core: if the gate after G1 can be taken out with the later gates rewritten,
-- a circuit with one gate fewer computes the same function, against minimality.
theorem core (n : ℕ) (C : Circuit) (hmin : IsMinimalCircuit n C)
    (G1 G2 : List Gate) (g : Gate) (hC : C.gates = G1 ++ g :: G2)
    (τ : Gate → Gate) (out' : ℕ) (Inv : ℕ → List Bool → Prop) (Good : Gate → Prop)
    (hgood : ∀ h ∈ G2, Good h)
    (hτ : ∀ h, Good h → (τ h).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (τ h).inputs.length ≤ 2)
    (hlen : ∀ k W, Inv k W → n + G1.length < W.length)
    (hstep : ∀ k W z, Inv (k + 1) W → Inv k (W ++ [z]))
    (hgl : ∀ k W h, Inv (k + 1) W → Good h → gv (τ h) (W.eraseIdx (n + G1.length)) = gv h W)
    (hinit : ∀ x : Fin n → Bool,
      Inv G2.length (run G1 (List.ofFn x) ++ [gv g (run G1 (List.ofFn x))]))
    (hout : ∀ W, Inv 0 W →
      (W.eraseIdx (n + G1.length)).getD out' false = W.getD C.output false) : False := by
  obtain ⟨hfan, hmin'⟩ := hmin
  have hD : FanInTwo ⟨G1 ++ G2.map τ, out'⟩ := by
    intro h hh
    have hh' : h ∈ G1 ∨ ∃ h', h' ∈ G2 ∧ τ h' = h := by simpa using hh
    rcases hh' with hh' | ⟨h', hh', rfl⟩
    · exact hfan h (by rw [hC]; simp [hh'])
    · exact hτ h' (hgood h' hh')
  have hfun : circuitFun n ⟨G1 ++ G2.map τ, out'⟩ = circuitFun n C := by
    funext x
    have hW0 : (run G1 (List.ofFn x)).length = n + G1.length := by simp [run_length]
    have hs := sim (n + G1.length) τ Inv Good hlen hstep hgl G2 _ (hinit x) hgood
    have he : (run G1 (List.ofFn x) ++ [gv g (run G1 (List.ofFn x))]).eraseIdx (n + G1.length)
        = run G1 (List.ofFn x) := by
      rw [← hW0]
      exact eraseIdx_append_len _ _
    rw [he] at hs
    have hrun : run C.gates (List.ofFn x)
        = run G2 (run G1 (List.ofFn x) ++ [gv g (run G1 (List.ofFn x))]) := by
      rw [hC, run_append, run_cons]
      rfl
    show (run (G1 ++ G2.map τ) (List.ofFn x)).getD out' false
      = (run C.gates (List.ofFn x)).getD C.output false
    rw [run_append, hs.1, hrun]
    exact hout _ hs.2
  have h1 := hmin' _ hD hfun
  have h2 : (⟨G1 ++ G2.map τ, out'⟩ : Circuit).size + 1 = C.size := by
    simp only [Circuit.size, hC, List.length_append, List.length_map, List.length_cons]
    omega
  omega

-- The gate after G1 cannot copy an earlier wire.
theorem no_copy (n : ℕ) (C : Circuit) (hmin : IsMinimalCircuit n C)
    (G1 G2 : List Gate) (g : Gate) (hC : C.gates = G1 ++ g :: G2)
    (y : ℕ) (hy : y < n + G1.length)
    (hval : ∀ x : Fin n → Bool,
      gv g (run G1 (List.ofFn x)) = (run G1 (List.ofFn x)).getD y false) : False := by
  refine core n C hmin G1 G2 g hC (ren (n + G1.length) y) (rho (n + G1.length) y C.output)
    (fun _ W => n + G1.length < W.length ∧ W.getD (n + G1.length) false = W.getD y false) GoodF
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro h hh
    exact hmin.1 h (by rw [hC]; simp [hh])
  · intro h hh
    exact ren_fan _ _ h hh
  · intro k W hW
    exact hW.1
  · intro k W z hW
    refine ⟨by simp; omega, ?_⟩
    rw [getD_append_lt W z _ hW.1, getD_append_lt W z _ (by omega)]
    exact hW.2
  · intro k W h hW _
    exact gv_ren _ _ W h (by rw [getD_erase_lt W _ y hy]; exact hW.2.symm)
  · intro x
    have hW0 : (run G1 (List.ofFn x)).length = n + G1.length := by simp [run_length]
    have e1 : (run G1 (List.ofFn x) ++ [gv g (run G1 (List.ofFn x))]).getD (n + G1.length) false
        = gv g (run G1 (List.ofFn x)) := by
      rw [← hW0]
      exact getD_append_len _ _
    have e2 : (run G1 (List.ofFn x) ++ [gv g (run G1 (List.ofFn x))]).getD y false
        = (run G1 (List.ofFn x)).getD y false :=
      getD_append_lt _ _ _ (by omega)
    refine ⟨by simp [hW0], ?_⟩
    rw [e1, e2]
    exact hval x
  · intro W hW
    exact rho_spec _ _ W (by rw [getD_erase_lt W _ y hy]; exact hW.2.symm) C.output

-- The gate after G1 cannot be always false.
theorem no_false (n : ℕ) (C : Circuit) (hmin : IsMinimalCircuit n C)
    (G1 G2 : List Gate) (g : Gate) (hC : C.gates = G1 ++ g :: G2)
    (hval : ∀ x : Fin n → Bool, gv g (run G1 (List.ofFn x)) = false) : False := by
  refine core n C hmin G1 G2 g hC
    (ren (n + G1.length) (n + G1.length + 1 + G2.length))
    (rho (n + G1.length) (n + G1.length + 1 + G2.length) C.output)
    (fun k W => n + G1.length < W.length ∧ W.length + k ≤ n + G1.length + 1 + G2.length ∧
      W.getD (n + G1.length) false = false) GoodF
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro h hh
    exact hmin.1 h (by rw [hC]; simp [hh])
  · intro h hh
    exact ren_fan _ _ h hh
  · intro k W hW
    exact hW.1
  · intro k W z hW
    refine ⟨by simp; omega, by simp; omega, ?_⟩
    rw [getD_append_lt W z _ hW.1]
    exact hW.2.2
  · intro k W h hW _
    exact gv_ren _ _ W h (by rw [getD_erase_big W _ _ (by omega), hW.2.2])
  · intro x
    have hW0 : (run G1 (List.ofFn x)).length = n + G1.length := by simp [run_length]
    have e1 : (run G1 (List.ofFn x) ++ [gv g (run G1 (List.ofFn x))]).getD (n + G1.length) false
        = gv g (run G1 (List.ofFn x)) := by
      rw [← hW0]
      exact getD_append_len _ _
    refine ⟨by simp [hW0], by simp [hW0], ?_⟩
    rw [e1]
    exact hval x
  · intro W hW
    exact rho_spec _ _ W (by rw [getD_erase_big W _ _ (by omega), hW.2.2]) C.output

def GoodT (h : Gate) : Prop :=
  (h.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ h.inputs.length ≤ 2) ∧
    (h.op = GateOp.not → h.inputs.length ≤ 1)

-- The gate after G1 cannot be always true.
theorem no_true (n : ℕ) (C : Circuit) (hmin : IsMinimalCircuit n C)
    (hnc : ∃ (x y : Fin n → Bool), circuitFun n C x ≠ circuitFun n C y)
    (hnot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (G1 G2 : List Gate) (g : Gate) (hC : C.gates = G1 ++ g :: G2)
    (hval : ∀ x : Fin n → Bool, gv g (run G1 (List.ofFn x)) = true) : False := by
  by_cases ho : C.output = n + G1.length
  · obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    have key : ∀ z : Fin n → Bool, circuitFun n C z = true := by
      intro z
      have hW0 : (run G1 (List.ofFn z)).length = n + G1.length := by simp [run_length]
      have e1 : (run G1 (List.ofFn z) ++ [gv g (run G1 (List.ofFn z))]).getD (n + G1.length) false
          = gv g (run G1 (List.ofFn z)) := by
        rw [← hW0]
        exact getD_append_len _ _
      show (run C.gates (List.ofFn z)).getD C.output false = true
      rw [hC, run_append, run_cons, ho, run_getD_lt _ _ _ (by simp [step, hW0])]
      show (run G1 (List.ofFn z) ++ [gv g (run G1 (List.ofFn z))]).getD (n + G1.length) false = true
      rw [e1]
      exact hval z
    rw [key x, key y]
  · refine core n C hmin G1 G2 g hC (elimT (n + G1.length)) (shift (n + G1.length) C.output)
      (fun _ W => n + G1.length < W.length ∧ W.getD (n + G1.length) false = true) GoodT
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro h hh
      have hm : h ∈ C.gates := by rw [hC]; simp [hh]
      exact ⟨hmin.1 h hm, hnot h hm⟩
    · intro h hh
      exact elimT_fan _ h hh.1.1 hh.1.2
    · intro k W hW
      exact hW.1
    · intro k W z hW
      refine ⟨by simp; omega, ?_⟩
      rw [getD_append_lt W z _ hW.1]
      exact hW.2
    · intro k W h hW hh
      exact gv_elimT _ W h hW.2 hh.1.1 hh.2
    · intro x
      have hW0 : (run G1 (List.ofFn x)).length = n + G1.length := by simp [run_length]
      have e1 : (run G1 (List.ofFn x) ++ [gv g (run G1 (List.ofFn x))]).getD (n + G1.length) false
          = gv g (run G1 (List.ofFn x)) := by
        rw [← hW0]
        exact getD_append_len _ _
      refine ⟨by simp [hW0], ?_⟩
      rw [e1]
      exact hval x
    · intro W hW
      exact shift_spec _ W C.output ho

-- Values of the small gate shapes.
theorem gv_and1 (W : List Bool) (a : ℕ) : gv ⟨GateOp.and, [a]⟩ W = W.getD a false := by
  show ([W.getD a false].all id) = W.getD a false
  simp

theorem gv_and2 (W : List Bool) (a b : ℕ) :
    gv ⟨GateOp.and, [a, b]⟩ W = (W.getD a false && W.getD b false) := by
  show ([W.getD a false, W.getD b false].all id) = (W.getD a false && W.getD b false)
  simp

theorem gv_or1 (W : List Bool) (a : ℕ) : gv ⟨GateOp.or, [a]⟩ W = W.getD a false := by
  show ([W.getD a false].any id) = W.getD a false
  simp

theorem gv_or2 (W : List Bool) (a b : ℕ) :
    gv ⟨GateOp.or, [a, b]⟩ W = (W.getD a false || W.getD b false) := by
  show ([W.getD a false, W.getD b false].any id) = (W.getD a false || W.getD b false)
  simp

theorem gv_not1 (W : List Bool) (a : ℕ) : gv ⟨GateOp.not, [a]⟩ W = !(W.getD a false) := rfl

theorem main (n : ℕ) (C : Circuit) (hmin : IsMinimalCircuit n C)
    (hnc : ∃ (x y : Fin n → Bool), circuitFun n C x ≠ circuitFun n C y)
    (hnot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (j : ℕ) (g : Gate) (hj : C.gates[j]? = some g) :
    (∀ i ∈ g.inputs, i < n + j) ∧ g.inputs.Nodup ∧
      (g.op = GateOp.not → g.inputs.length = 1) ∧
      (g.op ≠ GateOp.not → g.inputs.length = 2) := by
  obtain ⟨G1, G2, hC, rfl⟩ : ∃ G1 G2, C.gates = G1 ++ g :: G2 ∧ G1.length = j := by
    obtain ⟨hjlt, hjg⟩ := List.getElem?_eq_some_iff.mp hj
    refine ⟨C.gates.take j, C.gates.drop (j + 1), ?_, ?_⟩
    · rw [← hjg, ← List.drop_eq_getElem_cons hjlt, List.take_append_drop]
    · rw [List.length_take]
      omega
  have hgmem : g ∈ C.gates := by rw [hC]; simp
  obtain ⟨hop, hlen⟩ := hmin.1 g hgmem
  have hng := hnot g hgmem
  have hcopy : ∀ y, y < n + G1.length →
      ¬ (∀ x : Fin n → Bool,
        gv g (run G1 (List.ofFn x)) = (run G1 (List.ofFn x)).getD y false) :=
    fun y hy hv => no_copy n C hmin G1 G2 g hC y hy hv
  have hfalse : ¬ (∀ x : Fin n → Bool, gv g (run G1 (List.ofFn x)) = false) :=
    fun hv => no_false n C hmin G1 G2 g hC hv
  have htrue : ¬ (∀ x : Fin n → Bool, gv g (run G1 (List.ofFn x)) = true) :=
    fun hv => no_true n C hmin hnc hnot G1 G2 g hC hv
  have hbig : ∀ (x : Fin n → Bool) (i : ℕ), n + G1.length ≤ i →
      (run G1 (List.ofFn x)).getD i false = false := by
    intro x i hi
    apply List.getD_eq_default
    simp [run_length]
    omega
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · exact absurd (fun x => rfl) htrue
    · exfalso
      by_cases ha : a < n + G1.length
      · exact hcopy a ha (fun x => gv_and1 _ a)
      · exact hfalse (fun x => by rw [gv_and1]; exact hbig x a (by omega))
    · have ha : a < n + G1.length := by
        by_contra ha
        exact hfalse (fun x => by rw [gv_and2, hbig x a (by omega)]; rfl)
      have hb : b < n + G1.length := by
        by_contra hb
        exact hfalse (fun x => by rw [gv_and2, hbig x b (by omega)]; exact Bool.and_false _)
      have hab : a ≠ b := by
        rintro rfl
        exact hcopy a ha (fun x => by rw [gv_and2]; exact Bool.and_self _)
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact ha
        · exact hb
      · simp [hab]
      · intro h
        cases h
      · intro _
        rfl
    · exfalso
      simp only [List.length_cons] at hlen
      omega
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · exact absurd (fun x => rfl) hfalse
    · exfalso
      by_cases ha : a < n + G1.length
      · exact hcopy a ha (fun x => gv_or1 _ a)
      · exact hfalse (fun x => by rw [gv_or1]; exact hbig x a (by omega))
    · have ha : a < n + G1.length := by
        by_contra ha
        by_cases hb : b < n + G1.length
        · exact hcopy b hb (fun x => by rw [gv_or2, hbig x a (by omega)]; exact Bool.false_or _)
        · exact hfalse (fun x => by rw [gv_or2, hbig x a (by omega), hbig x b (by omega)]; rfl)
      have hb : b < n + G1.length := by
        by_contra hb
        exact hcopy a ha (fun x => by rw [gv_or2, hbig x b (by omega)]; exact Bool.or_false _)
      have hab : a ≠ b := by
        rintro rfl
        exact hcopy a ha (fun x => by rw [gv_or2]; exact Bool.or_self _)
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact ha
        · exact hb
      · simp [hab]
      · intro h
        cases h
      · intro _
        rfl
    · exfalso
      simp only [List.length_cons] at hlen
      omega
  · have hl : ins.length ≤ 1 := hng rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
    · exact absurd (fun x => rfl) htrue
    · have ha : a < n + G1.length := by
        by_contra ha
        exact htrue (fun x => by rw [gv_not1, hbig x a (by omega)]; rfl)
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rw [hi]
        exact ha
      · simp
      · intro _
        rfl
      · intro h
        exact absurd rfl h
    · exfalso
      simp only [List.length_cons] at hl
      omega

end PEqualNP.Outside.L_meta_3592

theorem PEqualNP.Outside.L_meta_3592 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit x1 x2 → (∃ (x4 : Fin x1 → Bool) (x5 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x4 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x5) → (∀ x5 ∈ x2.gates, x5.op = PEqualNP.CircuitLowerBounds.GateOp.not → x5.inputs.length ≤ (1 : ℕ)) → ∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x6]? = Option.some x7 → (∀ x9 ∈ x7.inputs, x9 < x1 + x6) ∧ x7.inputs.Nodup ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.not → x7.inputs.length = (1 : ℕ)) ∧ (x7.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → x7.inputs.length = (2 : ℕ)) := by
  intro n C hmin hnc hnot j g hj
  exact PEqualNP.Outside.L_meta_3592.main n C hmin hnc hnot j g hj
