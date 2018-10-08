# Unicode in Lean

A list of commonly used symbols in Lean. 
I recommend using this document by copy and pasting the symbol you want into a `.lean` file in vscode and then hovering over the symbol to see the completion string for it. 
I've taken the unicode charts and pruned out the pointless characters that nobody uses.

I am using the font [PragmataPro](https://www.fsd.it/shop/fonts/pragmatapro/?attribute_weights=PragmataPro+Regular+with+PP+Mono+Regular&attribute_license-for=desktop). 
In which all of the below symbols are rendered nicely and distinguishably.
I like PragmataPro because it keeps to the letter grid even with the more obscure symbols. It also gives two characters of space to arrows like `→`. The bad news is you have to pay for this font.

### A warning
There are serious risks in allowing any unicode symbol to be a valid Lean identifier:
There are so many caveats to Unicode:
- There are unicode characters that don't render to anything. Null characters.
- There are many different unicode characters for spaces. Chart [`U+2000`](http://www.unicode.org/charts/PDF/U2000.pdf) is particularly dangerous.
- Some glyphs (what the character looks like) will have different unicode code points (the number `U+XXXX`). Eg `ℝ` and `𝕉`.
- Some of the [Mathematical Alphanumeric Symbols](http://www.unicode.org/charts/PDF/U1D400.pdf) glyphs look the same as the ASCII symbols in some programming fonts. It looks like Lean outright refuses to accept a `.lean` file that uses some of these codepoints. Which is good.

Why is this a problem? Because it means we can appear to prove impossible results:
```lean
def A := true -- hide this line deep in another lean file.

def Α := false -- this is actually a capital alpha.
example : A := trivial -- Lean is inconsistent!?!?!?
```

## Letters
```
 A B C D E F G H I J K L M N O P Q R S T U V W X Y Z
 a b c d e f g h i j k l m n o p q r s t u v w x y z
 0 1 2 3 4 5 6 7 8 9
```
### Greek
I've removed the letters which clash with latin letters.
```
 Γ Δ Θ Λ Ξ Π Σ Υ Φ Ψ Ω
 α β γ δ ε ζ η θ ι κ λ μ ν ξ π ρ ς σ τ υ φ χ ψ ω 
 ∂   ϑ ϰ ϕ ϱ ϖ
```
## Letter-like mathematical symbols in unicode.
The unicode standard messes up how it codes mathematical symbols. This is because there are two charts:
- [Letterlike Symbols](http://www.unicode.org/charts/PDF/U2100.pdf) `U+2100-214F`
- [Mathematical Alphanumeric Symbols](http://www.unicode.org/charts/PDF/U1D400.pdf) `U+1D400–1D7FF`

Some characters such as what we would write as `\mathbb{R}` in LaTeX, appear in both of these charts. Both `U+211D` (`ℝ`) and `U+1D549` (`𝕉`) look like the symbol we use for the reals but are actually distinct unicode characters and so Lean will treat them differently. The actual unicode chart says `U+1D549` is blank but many fonts render it to look like the `U+211D`. I think the convention is to use the `U+2100-214F` chart unless it doesn't have your character, and then use the `U+1D400–1D7FF` chart.
### The 'letterlike symbols`
```
U+2100  ℀ ℁ ℂ ℃ ℄ ℅ ℆ ℇ ℈ ℉ ℊ ℋ ℌ ℍ ℎ ℏ
U+2110  ℐ ℑ ℒ ℓ ℔ ℕ № ℗ ℘ ℙ ℚ ℛ ℜ ℝ ℞ ℟
U+2120  ℠ ℡ ™ ℣ ℤ ℥ Ω ℧ ℨ ℩ K Å ℬ ℭ ℮ ℯ
U+2130  ℰ ℱ Ⅎ ℳ ℴ ℵ ℶ ℷ ℸ ℹ ℺ ℻ ℼ ℽ ℾ ℿ
U+2140  ⅀ ⅁ ⅂ ⅃ ⅄ ⅅ ⅆ ⅇ ⅈ ⅉ ⅊ ⅋ ⅌ ⅍ ⅎ ⅏
```
## Chart __1D400–1D7FF__
All of the following characters are exclusively in the `U+1D400–1D7FF` chart. I have omitted the characters that don't look good in my font (PragmataPro) and which are not allowed in Lean. 
I have also omitted characters that clash with the `letterlike symbols` chart.
<!--
### Mathematical Bold
[WARNING] These are not in Lean yet.
```
 𝐀 𝐁 𝐂 𝐃 𝐄 𝐅 𝐆 𝐇 𝐈 𝐉 𝐊 𝐋 𝐌 𝐍 𝐎 𝐏 𝐐 𝐑 𝐒 𝐓 𝐔 𝐕 𝐖 𝐗 𝐘 𝐙 
 𝐚 𝐛 𝐜 𝐝 𝐞 𝐟 𝐠 𝐡 𝐢 𝐣 𝐤 𝐥 𝐦 𝐧 𝐨 𝐩 𝐪 𝐫 𝐬 𝐭 𝐮 𝐯 𝐰 𝐱 𝐲 𝐳 
 𝟎 𝟏 𝟐 𝟑 𝟒 𝟓 𝟔 𝟕 𝟖 𝟗 
```
### Mathematical Italic
[WARNING] These are not in Lean yet.
```
 𝐴 𝐵 𝐶 𝐷 𝐸 𝐹 𝐺 𝐻 𝐼 𝐽 𝐾 𝐿 𝑀 𝑁 𝑂 𝑃 𝑄 𝑅 𝑆 𝑇 𝑈 𝑉 𝑊 𝑋 𝑌 𝑍 
 𝑎 𝑏 𝑐 𝑑 𝑒 𝑓 𝑔 𝑕 𝑖 𝑗 𝑘 𝑙 𝑚 𝑛 𝑜 𝑝 𝑞 𝑟 𝑠 𝑡 𝑢 𝑣 𝑤 𝑥 𝑦 𝑧 
 𝛤 𝛥 𝛩 𝛬 𝛯 𝛱 𝛳 𝛴 𝛶 𝛷 𝛸 𝛹 𝛺 𝛻 
 𝛼 𝛽 𝛾 𝛿 𝜀 𝜁 𝜂 𝜃 𝜄 𝜅 𝜆 𝜇 𝜈 𝜉 𝜋 𝜌 𝜍 𝜎 𝜏 𝜐 𝜑 𝜒 𝜓 𝜔 
 𝜕 𝜖 𝜗 𝜘 𝜙 𝜚 𝜛 
```
-->
### Mathematical Script
Type with `\McX`
```
 𝒜   𝒞 𝒟     𝒢     𝒥 𝒦     𝒩 𝒪 𝒫 𝒬   𝒮 𝒯 𝒰 𝒱 𝒲 𝒳 𝒴 𝒵 
 𝒶 𝒷 𝒸 𝒹   𝒻   𝒽 𝒾 𝒿 𝓀 𝓁 𝓂 𝓃   𝓅 𝓆 𝓇 𝓈 𝓉 𝓊 𝓋 𝓌 𝓍 𝓎 𝓏 
```
I am omitting _Mathematical Bold Script_ because it looks too similar.
### Mathematical Fraktur
Type with `\MfX`
```
 𝔄 𝔅   𝔇 𝔈 𝔉 𝔊     𝔍 𝔎 𝔏 𝔐 𝔑 𝔒 𝔓 𝔔   𝔖 𝔗 𝔘 𝔙 𝔚 𝔛 𝔜   
 𝔞 𝔟 𝔠 𝔡 𝔢 𝔣 𝔤 𝔥 𝔦 𝔧 𝔨 𝔩 𝔪 𝔫 𝔬 𝔭 𝔮 𝔯 𝔰 𝔱 𝔲 𝔳 𝔴 𝔵 𝔶 𝔷 
```
I am omitting _Mathematical Bold Fraktur_ because it looks too similar.
### Mathematical Double-Struck
Type with `\bbX`.
```
 𝔸 𝔹   𝔻 𝔼 𝔽 𝔾   𝕀 𝕁 𝕂 𝕃 𝕄   𝕆       𝕊 𝕋 𝕌 𝕍 𝕎 𝕏 𝕐   
 𝕒 𝕓 𝕔 𝕕 𝕖 𝕗 𝕘 𝕙 𝕚 𝕛 𝕜 𝕝 𝕞 𝕟 𝕠 𝕡 𝕢 𝕣 𝕤 𝕥 𝕦 𝕧 𝕨 𝕩 𝕪 𝕫 
 𝟘 𝟙 𝟚 𝟛 𝟜 𝟝 𝟞 𝟟 𝟠 𝟡
```

## Accents and so on.

I am mostly against decorating letters with accents so I am not in a rush to fill out this section. There are also many Unicode caveats. For example:

- `ë` is `U+00EB` (Latin)
- `ё` is `U+0450` (Cyrillic)
- `e̎` is `U+0065 U+0308` and uses a [combining diaeresis](https://www.unicode.org/charts/PDF/U0300.pdf). Sometimes the combining marks look nice and sometimes the font butchers them.

It's an absolute minefield.

## Subscripts and superscripts

```
¹ ² ³
U+2070  ⁰ ⁱ   ⁴ ⁵ ⁶ ⁷ ⁸ ⁹ ⁺ ⁻ ⁼ ⁽ ⁾ ⁿ
U+2080  ₀ ₁ ₂ ₃ ₄ ₅ ₆ ₇ ₈ ₉ ₊ ₋ ₌ ₍ ₎
U+2090  ₐ ₑ ₒ ₓ ₔ ₕ ₖ ₗ ₘ ₙ ₚ ₛ ₜ
```

## Brackets
```
( ) [ ] { }
⦃ ⦄ ⟦ ⟧ ⟨ ⟩ ⟪ ⟫ 
‹ › « » 
⁅ ⁆ ⌈ ⌉ ⌊ ⌋ ⌜ ⌝ ⌞ ⌟
```
These don't have completions but I like them:
```
⟮ ⟯ ⟬ ⟭   
⦋ ⦌ ⦍ ⦎ ⦏ ⦐
⦉ ⦊ ⦅ ⦆ ⦇ ⦈ ⨴ ⨵
```

## Symbols
```
∀ ∂ ∃ ∄ ∅ ∝ ∞ √ ∛ ∜ ∫ ∮ ∱ ∲ ∳ ∓ ± ∆ ∇
```
### big ops
```
⋀ ⋁ ⋂ ⋃ ⨅ ⨆ ∏ ∐ ∑ ⨁ ⨂ ⨀ 
```
### products 
```
∗ ∘ ∙ ⋄ ⋅ ⋆ ⋇ ⋈ ※
⊍ ⊎ 
⊕ ⊖ ⊗ ⊘ ⊙ ⊚ ⊛ ⊜ ⊝ 
⊞ ⊟ ⊠ ⊡ 
∴ ∵ ⁖ ⋮ ⋯ ⁘ ⁙
```


### relations
```
< > ≤ ≥ ≮ ≯ ≰ ≱ ∧ ∨
≺ ≻ ≼ ≽ ⊀ ⊁     ⋏ ⋎
⊂ ⊃ ⊆ ⊇ ⊄ ⊅ ⊈ ⊉ ∩ ∪
∈ ∋     ∉ ∌
⊲ ⊳ ⊴ ⊵         
⊏ ⊐ ⊑ ⊒         ⊓ ⊔ 
⋐⋑            ⋒⋓

≃ ≄ ≅ ≇ ≈ ≉ ≊ ≋ ≍ ≎ ≏ ≐ ≑ ≒ ≓
≖ ≗ ≘ ≙ ≚ ≛ ≜ ≝ ≞ ≟ ≠ ≡ ≢ ≣
≪ ≫ ⋘ ⋙
⊢ ⊣ ⊤ ⊥ ⊦ ⊧ ⊨ ⊩ ⊪ ⊫
```
## arrows
```
← ↑ → ↓ ↔ ↕ ⟵ ⟶ ⟷
⇐ ⇑ ⇒ ⇓ ⇔ ⇕ ⟸ ⟹ ⟺
↤ ↥ ↦ ↧      ⟻ ⟼
⇜   ⇝   ↭   ⬳ ⟿ 
↞ ↟ ↠ ↡ 
↜   ↝ 
↢   ↣ 
⇇ ⇈ ⇉ ⇊ 
⇚ ⟰ ⇛ ⟱

↫ ↬ ↩ ↪ ↯ ↺ ↻ ⇶
```
### arrows with evil twins
I stipulate using these:
```
↼ ↾ ⇀ ⇂  
⇄ ⇅ 
⇋ ⥮
```
And avoiding these:
``` 
↽ ↿ ⇁ ⇃
⇆ ⇵
⇌ ⥯ 
```
### arrows with no completions
```
⤆   ⤇        ⟽ ⟾
⇠ ⇡ ⇢ ⇣
⇦ ⇧ ⇨ ⇩ ⬄ ⇳
⬅ ⬆ ⮕ ⬇ ⬌ ⬍
⇤ ⤒ ⇥ ⤓
⇷ ⤉ ⇸ ⤈ ⇹  
⇺ ⇞ ⇻ ⇟ ⇼
⤺   ⤻ ⤸ 
⇴ ⟴
```

## Emoji

Emoji are not allowed as identifiers. Maybe one day we will be able to finish off a lemma with `show 🤯, by exact 💩 💥`. But today is not that day.

<!-- 

        0 1 2 3 4 5 6 7 8 9 A B C D E F
 U+0300 à á â ã ā a̅ ă ȧ ä ả å a̋ ǎ a̍ a̎ ȁ
 U+0310 a̐ ȃ a̒ a̓ a̔ a̕ a̖ a̗ a̘ a̙ a̚ a̛ a̜ a̝ a̞ a̟
 U+0320 a̠ a̡ a̢ ạ a̤ ḁ a̦ a̧ ą a̩ a̪ a̫ a̬ a̭ a̮ a̯
 U+0330 a̰ a̱ a̲ a̳ a̴ a̵ a̶ a̷ a̸ a̹ a̺ a̻ a̼ a̽ a̾ a̿
 U+0340 à á a͂ a̓ ẍ á aͅ a͆ a͇ a͈ a͉ a͊ a͋ a͌ a͍ a͎ ͏
 U+0350 a͐ a͑ a͒ a͓ a͔ a͕ a͖ a͗ a͘ a͙ a͚ a͛ xx͜ xx͝ xx͞ xx͟
 U+0360 az͠ ab͡ ad͢
   
   
   A B C D E F G H   I J K L M N O P  Q R  S T U V W X Y Z
-| α β ⌜ ↓ = ‹ γ ⟶ ∩ ⋈ ̨ ← ≞ ∋ ∘ ↣ ∎ → ß ▸ ↑ ̌  ℘ × ɏ ζ
a| å       æ               ∀ ∐∧   ⌶       ∗   ₳              
b| ∽ 𝔹 ℂ   β         ⋂    ▪   ∋ ⊥ ℙ  ℚ ℝ  ⅀   •     ⊠   ℤ 
c| ∩   ç ḑ ȩ   ģ ḩ   ●   ķ ⌞   ņ ⬝      ŗ  ş ţ       
d| †     ↡       ð   ◆     ↙    ⬝      ↘               ↯
e|                         ℓ — –  ε  =      η €     ∃
f| ℻                             ∀      ‹      λ
g| γ       ≥   ≫     ℷ     ⊓   ≩        ‘    ⋗ ₲ ≩        
h|   ℏ     ͱ                            ₴      

 -->