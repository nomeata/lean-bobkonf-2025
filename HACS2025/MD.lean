
structure Compression (n : Nat) where
  State : Type
  iv : State
  f : State → Vector UInt8 n → State
  final : State → Array UInt8

def hsh (hn : 0 < n) (c : Compression n) (as : Array UInt8) : Array UInt8 :=
  go 0 c.iv
where
  go i s :=
    if h : i + n < as.size then
      let v := Vector.mk (as.extract i (i + n)) (by simp; omega)
      let s' := c.f s v
      go (i + n) s'
    else if h' : i < as.size then
      let v := Vector.mk (as.extract i as.size ++ mkArray (n - (as.size - i)) 0) <| by
        simp
        omega
      let s' := c.f s v
      go (i + n) s'
    else
      c.final s
  termination_by as.size - i

structure StreamHash where
  n : Nat
  hn : 0 < n
  c : Compression n
  s : c.State
  buf : Array UInt8
  hsize : buf.size < n

def StreamHash.init {n : Nat} (hn : 0 < n) (c : Compression n) : StreamHash where
  n := n
  hn := hn
  c := c
  s := c.iv
  buf := #[]
  hsize := by simp; omega

def StreamHash.push (s : StreamHash) (b : UInt8) : StreamHash :=
  let buf' := s.buf.push b
  if h : buf'.size < s.n then
    { s with buf := buf', hsize := h }
  else
    let v := Vector.mk buf' <| by
      have := s.hsize; simp [buf'] at *; omega
    let s' := s.c.f s.s v
    { s with s := s', buf := #[], hsize := by simp; exact s.hn }

def StreamHash.get (s : StreamHash) : Array UInt8 :=
  if h : 0 < s.buf.size then
    let v := Vector.mk (s.buf ++ mkArray (s.n - s.buf.size) 0) <| by
      have := s.hsize
      simp
      omega
    let s' := s.c.f s.s v
    s.c.final s'
  else
    s.c.final s.s

theorem correctness (hn : 0 < n) (c : Compression n) (as : Array UInt8) :
    hsh hn c as =
      (as.foldl (StreamHash.push) (StreamHash.init hn c)).get := by
  unfold hsh StreamHash.init
  simpa using go 0 _
where
  go i s :
    hsh.go hn c as (i*n) s =
      ((as.extract (i * n)).foldl (StreamHash.push) {n, hn, c, s, buf := #[], hsize := (by simp; omega)}).get := by
    unfold hsh.go
    split
    · have : as.extract (i * n) = as.extract (i * n) (i * n + n) ++ as.extract (i * n + n) := sorry
      rw [this]; clear this
      rw [Array.foldl_append]
      conv => lhs; simp
      rewrite (occs := [1]) [← Nat.succ_mul i n]
      rw [go]
      simp [Nat.succ_mul]
      congr 2
      sorry
    · split
      · sorry
      · rw [show as.extract (i * n) = #[] by simp; omega]
        simp
        simp [StreamHash.get]
