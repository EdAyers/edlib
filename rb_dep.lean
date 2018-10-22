/- Mirrors `rb.lean` but with dependent types from the start -/


namespace rb_dep
universes u v
section rb
open nat
inductive col | Red | Black
open col
inductive node (K : Type u) (A : Type v) : col → ℕ → Type max u v
|Leaf {} : node Black 0
|Rd {n}  (l : node Black n) (v : K × A) (r : node Black n) : node Red n
|Bk {cl cr n} (l : node cl n) (v : K × A) (r : node cr n) : node Black (succ n)
open node
inductive growth (K : Type u) (A : Type v) : ℕ → Type max u v
|sproutl {cll clr cr n} (ll : node K A cll n) (lv : K×A) (lr : node K A clr n) (v : K×A) (r : node K A cr n) : growth n
|sproutr {cl crl crr n} (l : node K A cl n) (v : K×A) (rl : node K A crl n) (rv : K×A) (rr : node K A crr n) : growth n
|sprout {c n} (t : node K A c n) : growth n
open growth

variables {K : Type u} {A : Type v} [has_lt K] [decidable_rel ((<) : K → K → Prop)]
variables {n : ℕ} {cl cr c : col}
def get_col : Π {c}, node K A c n → Σ c, node K A c n
|Black t := ⟨Black, t⟩
|Red t := ⟨Red, t⟩
instance : has_coe (node K A c n) (Σ c, node K A c n) := ⟨λ t, get_col t⟩ 

def ins_aux.type (K : Type u) (A : Type v) : col → Type (max u v)
| Black := 

def ins_aux (k : K) (a : A) : Π {c n}, node K A c n → Σ c, node K A c n
|Black 0 Leaf := Rd Leaf ⟨k,a⟩ Leaf
|Red n (Rd l v r) := -- l and r are both Black. So `ins_aux l` is either black, balanced, or sprouting
    if k < v.1 then
        match ins_aux l with
        |⟨Red, Rd ll lv lr⟩ := sproutl ll lv lr v r 
        |⟨Black, l⟩ := stay (Rd l v r)
        end
    else if k > v.1 then Rd l v (ins_aux r) -- R
    else Rd l ⟨k,a⟩ r -- R
|Black n (Bk l v r) :=
    if k < v.1 then
        match ins_aux l with
        | (sproutl a x b y c) := Rd (Bk a x b) y (Bk c v r)
        | (sproutr a x b y c) := Rd (Bk a x b) y (Bk c v r)
        | (stay l)  := Bk l v r
        end
    else if k > v.1 then
        match ins_aux r with
        | (sproutl b w c z d) := Rd (Bk l v b) w (Bk c z d)
        | (sproutr b w  c z d) := Rd (Bk l v b) w (Bk c z d)
        | (stay r) := Bk l v r
        end
    else stay $ Bk l ⟨k,a⟩ r -- B

end rb
end rb_dep
