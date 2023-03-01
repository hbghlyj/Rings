<TeXmacs|2.1.2>

<style|<tuple|article|number-long-article>>

<\body>
  <\hide-preamble>
    <new-remark|observation|Observation>

    <assign|remark-name|<\macro|name>
      <em|<arg|name>>
    </macro>>

    <assign|example-text|<macro|<inactive|<localize|Example>>>>

    <assign|example|<\macro|body>
      <surround|<compound|next-example>||<compound|render-theorem|<compound|example-numbered|<compound|example-text>|<compound|the-example>>|<arg|body>>>
    </macro>>

    <assign|render-theorem|<\macro|which|body>
      <render-enunciation|<theorem-name|<arg|which><theorem-sep>>|<arg|body>>
    </macro>>
  </hide-preamble>

  <section|Rings>

  A set <math|R> containing two (possibly equal) elements 0 and 1, and
  supporting two binary operations + and\<times\>is a <strong|ring> if

  <\itemize-dot>
    <item><math|R> equipped with + is a commutative group;

    <item>\<times\> is an associative binary operation on <math|R> with
    identity 1;

    <item>\<times\> is distributive over +.
  </itemize-dot>

  Occasionally we shall have multiple rings and it will be instructive to
  clarify which particular ring we are referring to. We shall do this with
  subscripts writing, for example, <math|+<rsub|R>> or <math|1<rsub|R>>
  instead of + and 1 above. Identity of associative binary operations is
  unique when it exists.

  The operation + is the <strong|addition> of the ring, the set <math|R> with
  the operation + is the <strong|additive group> of the ring and we denote
  its identity 0, the <strong|zero> of the ring, and . For each
  <math|x\<in\>R> we write <math|-x> for the unique inverse of <math|x>
  w.r.t. addition, and the map <math|R\<rightarrow\>R;x\<mapsto\>-x> is the
  <strong|negation> of the ring; we write <math|x-y> for
  <math|x+<around*|(|-y|)>>.

  We call a map <math|\<phi\>:R\<rightarrow\>S> between rings
  <strong|additive> if it is a homomorphism of the additive groups.

  <\observation>
    Identities are self-inverse so \<minus\>0 = 0; double inversion is the
    identity map i.e. <math|-<around*|(|-x|)>=x> for all <math|x\<in\>R>; and
    inversion is a homomorphism of the additive group since a group operation
    is commutative (if and) only if inversion is a homomorphism of the group.

    Group homomorphisms map identities to identities and inverses to
    inverses, so if <math|\<phi\>:R\<rightarrow\>S> is additive then
    <math|\<phi\><around*|(|0<rsub|R>|)>=0<rsub|S>> and
    <math|\<phi\><around*|(|-x|)>=-\<phi\><around*|(|x|)>> for all
    <math|x\<in\>R>.
  </observation>

  The operation\<times\>is the <strong|multiplication> of the ring, and we
  write <math|x y> in place of <math|x\<times\>y>, and in the absence of
  parentheses multiplication precedes addition in the usual way. We say
  <math|R> is a <strong|commutative> ring if the multiplication is
  commutative.

  <\remark>
    The modern notion of commutative ring can be traced back to Emmy Noether
    [Noe21, \<#00A7\>1] (translated into English in [Ber14]), though unlike
    us her definition does not assume the multiplication has an identity;
    Poonen [Poo19] defends our position.
  </remark>

  We call a map <math|\<phi\>:R\<rightarrow\>S> between rings
  <strong|multiplicative> if <math|\<phi\><around*|(|x
  y|)>=\<phi\><around*|(|x|)>\<phi\><around*|(|y|)>> for all
  <math|x,y\<in\>R>, and we call it a <strong|ring homomorphism> if
  <math|\<phi\>> is additive, multiplicative, and
  <math|\<phi\><around*|(|1<rsub|R>|)>=1<rsub|S>>.

  <\observation>
    The composition of additive (resp. multiplicative) maps is additive
    (resp. multiplicative), and hence the composition of ring homomorphisms
    is a ring homomorphism.
  </observation>

  <\definition>
    For a set <math|A\<subset\>X> and a function <math|f:X\<rightarrow\>Y> we
    write <math|f<around*|(|A|)>\<assign\><around*|{|f<around*|(|x|)>:x\<in\>A|}>>.
  </definition>

  For sets <math|A\<subset\>X,B\<subset\>Y>, and a function
  <math|X\<times\>Y\<rightarrow\>Z> denoted by infixing the symbol
  <math|\<ast\>> between the two arguments, we write
  <math|A\<ast\>B\<assign\><around*|{|a\<ast\>b:a\<in\>A,b\<in\>B|}>>; and
  denoted by juxtaposing the two arguments, we write <math|A
  B\<assign\><around*|{|a b:a\<in\>A,b\<in\>B|}>>.

  For <math|x\<in\>X> and <math|y\<in\>Y>, in the case of infix notation we
  put <math|x\<ast\>A\<assign\><around*|{|x|}>\<ast\>A> and
  <math|A\<ast\>y\<assign\>A\<ast\><around*|{|y|}>>; and in the case of
  juxtaposition we put <math|x A\<assign\><around*|{|x|}>A> and <math|A
  y\<assign\>A<around*|{|y|}>>.

  <subsection|Units and the trivial ring>

  An element <math|x\<in\>R> is a <strong|unit> if it is invertible w.r.t.
  multiplication <em|i.e.> if there is some <math|y\<in\>R> such that <math|x
  y=y x=1>. We write<\footnote>
    Some authors (e.g. [Lan02, p84] and [Lam07, xiv]) write
    <math|R<rsup|\<ast\>>> for the group of units of <math|R>.
  </footnote> <math|U<around*|(|R|)>> for the set of units of <math|R>, and
  <math|R<rsup|\<ast\>>> for the set of non-zero elements of <math|R>.
  Inverses w.r.t. associative binary operations are unique when they exist,
  so for <math|x\<in\>U<around*|(|R|)>> we can unambiguously write
  <math|x<rsup|-1>> for the inverse of <math|x>.

  <\observation>
    Given a ring <math|R>, if <math|x> and <math|y> are units then
    <math|<around*|(|y<rsup|-1>x<rsup|-1>|)><around*|(|x y|)>=1=<around*|(|x
    y|)><around*|(|y<rsup|-1>x<rsup|-1>|)>> and so <math|x y> is a unit, and
    the multiplication on <math|R> restricts to a well-defined binary
    operation on <math|U<around*|(|R|)>> making the latter into a group. This
    group is called the <strong|group of units> and it has identity
    <math|1<rsub|R>> and the inverse of <math|x> in the group
    <math|U<around*|(|R|)>> is <math|x<rsup|-1>>, that is the inverse of
    <math|x> in the ring <math|R>.
  </observation>

  <math|1<rsup|-1>=1> since identities are self-inverse; double inversion is
  the identity map i.e. <math|<around*|(|x<rsup|-1>|)><rsup|-1>=x> for all
  <math|x\<in\>U<around*|(|R|)>>; <math|<around*|(|x
  y|)><rsup|-1>=y<rsup|-1>x<rsup|-1>> for all
  <math|x,y\<in\>U<around*|(|R|)>>; and if <math|\<phi\>:R\<rightarrow\>S> is
  a ring homomorphism then <math|U<around*|(|R|)>\<rightarrow\>U<around*|(|S|)>;x\<mapsto\>\<phi\><around*|(|x|)>>
  is a well-defined group homomorphism with
  <math|\<phi\><around*|(|x<rsup|-1>|)>=\<phi\><around*|(|x|)><rsup|-1>>.

  <\remark>
    If <math|R> is a finite commutative ring then <math|U<around*|(|R|)>> is
    a finite commutative group, but exactly which finite commutative groups
    occur as the group of units of a ring is an open problem called Fuchs'
    problem [Fuc58, Problem 72, p299].
  </remark>

  Given <math|y\<in\>R>, the map <math|R\<rightarrow\>R;x\<mapsto\>y x>
  (resp. <math|R\<rightarrow\>R;x\<mapsto\>x y>) is called <strong|left>
  (resp. <strong|right>) <strong|multiplication> by <math|y>.

  <\observation>
    The fact that multiplication is distributive over addition in <math|R> is
    exactly to say that all the left and right multiplication maps are group
    homomorphisms of the additive group of <math|R>. If <math|x> is a unit
    then left and right multiplication by <math|x> are surjective.

    Group homomorphisms map identities to identities and inverses to
    inverses, so <math|x 0=0 x=0> for all <math|x\<in\>R> \U we say
    <strong|zero annihilates>; and <math|x <around*|(|-y|)>=-<around*|(|x
    y|)>=<around*|(|-x|)> y> for all <math|x,y\<in\>R> \U we say that
    <strong|negation distributes>. In particular <math|<around*|(|-1|)> x=-x>
    for all <math|x\<in\>R>.
  </observation>

  <\example>
    The set <math|<around*|{|0|}>>, with <math|1=0>, and addition and
    multiplication given by <math|0+0=0\<times\>0=0>, is a ring called the
    <strong|trivial> or <strong|zero> ring. A ring in which <math|1\<neq\>0>
    is called a <strong|non-trivial> ring.

    If <math|R> is not non-trivial then it is trivial: Indeed, since
    <math|0=1>, for all <math|x\<in\>R> we have <math|x=1*x=0*x=0> since zero
    annihilates and so <math|R=<around*|{|0|}>>. There is only one function
    into a set of size one, and so the addition and multiplication on
    <math|R> are uniquely determined and must be that of the trivial ring.
  </example>

  <\example>
    The <strong|zero map> <math|z<rsub|R>:R\<rightarrow\><around*|{|0|}>;x\<mapsto\>0>
    from a ring <math|R> to the trivial ring is a ring homomorphism.
  </example>

  <subsection|The integers and characteristic>

  We write <math|\<bbb-Z\>> for the integers; <math|\<bbb-N\><rsup|\<ast\>>>
  for the positive integers, that is {1, 2, 3, <text-dots>}; and
  <math|\<bbb-N\><rsub|0>> for the non-negative integers, that is {0, 1, 2,
  <text-dots>}.

  <\example>
    <math|\<bbb-Z\>> with their usual addition, multiplication, zero and 1
    form a non-trivial commutative ring for which
    <math|U<around*|(|\<bbb-Z\>|)>=<around*|{|-1,1|}>>.
  </example>

  <\theorem>
    <dueto|The One Ring<strong|<strong|<with|font-series|medium|<\footnote>
      Following [Tol04, Book I, Chapter 2, p66] one might describe the
      integers as the one ring (up to unique isomorphism) ruling (uniquely
      embedding in) all others.
    </footnote>>>>>Suppose that <math|R> is a ring. Then there is a unique
    ring homomorphism <math|\<chi\><rsub|R>:\<bbb-Z\>\<rightarrow\>R>, and we
    have

    <\equation*>
      \<chi\><rsub|R><around*|(|n-m|)>=<wide|1<rsub|R>+\<cdots\>+1<rsub|R>|\<wide-overbrace\>><rsup|n<text|
      times>>-<wide|1<rsub|R>+\<cdots\>+1<rsub|R>|\<wide-overbrace\>><rsup|m<text|
      times>>
    </equation*>
  </theorem>

  <\remark>
    To prove this we need to define <math|\<bbb-N\><rsup|\<ast\>>> and
    <math|\<bbb-Z\>> by Peano axiom, which roughly says <math|\<bbb-Z\>> is
    the smallest infinity. The proof is a series of inductions.
  </remark>

  If there is <math|n\<in\>\<bbb-N\><rsup|\<ast\>>> such that
  <math|\<chi\><rsub|R><around*|(|n|)>=0<rsub|R>> then there is a smallest
  such <math|n> and we call this the <strong|characteristic> of the ring; if
  there is no such <math|n> then the characteristic is said to be 0.

  <\example>
    For <math|N\<in\>\<bbb-N\><rsup|\<ast\>>>, we write
    <math|\<bbb-Z\><rsub|N>> for the integers modulo <math|N>. This is a
    commutative ring whose zero is <math|0<pmod|N>>, and with multiplicative
    identity <math|1<pmod|N>>. If <math|N=1> then <math|0\<equiv\>1<pmod|N>>
    and so the ring is trivial; otherwise it is non-trivial.
  </example>

  The characteristic of <math|\<bbb-Z\><rsub|N>> is <math|N> since
  <math|n\<in\>\<bbb-N\><rsup|\<ast\>>> has
  <math|\<chi\><rsub|\<bbb-Z\><rsub|N>><around*|(|n|)>=0<rsub|\<bbb-Z\><rsub|N>>>
  if and only if <math|n\<equiv\>0<pmod|N>>, so <math|n\<geqslant\>N> and
  <math|\<chi\><rsub|\<bbb-Z\><rsub|N>><around*|(|N|)>=0<rsub|\<bbb-Z\><rsub|N>>>.

  <subsection|Isomorphisms and subrings>

  A <strong|ring isomorphism> is a map <math|\<phi\>:R\<rightarrow\>S> that
  is a ring homomorphism with an inverse that is a ring homomorphism.

  <\example>
    The identity map <math|\<iota\><rsub|R>:R\<rightarrow\>R;x\<mapsto\>x> is
    a ring isomorphism.
  </example>

  A ring <math|S> is a <strong|subring> of a ring <math|R> if the inclusion
  map <math|j:S\<rightarrow\>R;s\<mapsto\>s> is a well-defined \U all this
  does is ensure that <math|S\<subset\>R> \U ring homomorphism called the
  <strong|inclusion homomorphism>; <math|S> is <strong|proper> if
  <math|S\<neq\>R>.

  <\example>
    <math|\<bbb-C\>> with its usual addition, multiplication, zero and 1 is a
    non-trivial commutative ring and <math|\<bbb-Z\>> is a subring of
    <math|\<bbb-C\>>.
  </example>

  <\observation>
    The 0 and 1 of a subring are the same as for the containing ring and so a
    subring of a non-trivial ring is non-trivial, and the characteristic of a
    subring is the same as the characteristic of the ring it is contained in.
  </observation>

  <with|font|Segoe UI Emoji|\<#26A0\>>In particular, the trivial ring is
  <em|not> a subring of any non-trivial ring <math|R> despite the fact that
  the inclusion map taking 0 to <math|0<rsub|R>> is both additive and
  multiplicative. It follows that the requirement that ring homomorphisms
  send 1 to 1 cannot be dropped from the definition.

  <\proposition>
    <dueto|Subring test>Suppose that <math|R> is a ring and
    <math|S\<subset\>R> has <math|1\<in\>S> and <math|x-y,x y\<in\>S> for all
    <math|x,y\<in\>S>. Then the addition and multiplication on <math|R>
    restrict to well-defined operations on <math|S> giving it the structure
    of a subring of <math|R>.
  </proposition>

  <\proof>
    First <math|S> is non-empty and <math|x-y\<in\>S> whenever
    <math|x,y\<in\>S> so by the subgroup test addition on <math|R> restricts
    to a well-defined binary operation on <math|S> giving it the structure of
    a commutative group. Since <math|S> is closed under multiplication,
    multiplication on <math|R> restricts to a well-defined binary operation
    on <math|S> that is <em|a fortiori> associative and distributive, and
    since <math|1\<in\>S> and 1 is <em|a fortiori> an identity for <math|S>,
    we have that <math|S> with these restricted operations is a ring. The map
    <math|S\<rightarrow\>R;s\<mapsto\>s> is then well-defined since <math|S>
    is a subset of <math|R>, and a ring homomorphism as required.
  </proof>

  Given a subset satisfying the hypotheses of the above lemma, we make the
  common abuse of calling it a subring on the understanding that we are
  referring to the restricted operations described by the lemma.

  <\example>
    For <math|d\<in\>\<bbb-N\><rsup|\<ast\>>> we write
    <math|\<bbb-Z\><around*|[|<sqrt|-d>|]>> for the set
    <math|<around*|{|z+w<sqrt|-d>:z,w\<in\>\<bbb-Z\>|}>>, which is a subring
    of <math|\<bbb-C\>> by the subring test. <math|\<bbb-Z\><around*|[|i|]>>
    \U the case <math|d=1> \U is called the set of <strong|Gaussian
    integers>.
  </example>

  We have <math|U<around*|(|\<bbb-Z\><around*|[|i|]>|)>=<around*|{|1,-1,i,-i|}>>:
  Certainly all the elements of <math|<around*|{|1,-1,i,-i|}>> are units. In
  the other direction, suppose <math|<around*|(|z+w*i|)><around*|(|x+y*i|)>=1>
  for some <math|x,y\<in\>\<bbb-Z\>>. Taking absolute values we have
  <math|<around*|(|z<rsup|2>+w<rsup|2>|)><around*|(|x<rsup|2>+y<rsup|2>|)>=1>,
  so <math|z<rsup|2>+w<rsup|2>=1>, and hence
  <math|<around*|(|z,w|)>\<in\><around*|{|<around*|(|1,0|)>,<around*|(|-1,0|)>,<around*|(|0,1|)>,<around*|(|0,-1|)>|}>>
  as required.

  For <math|d\<gtr\>1> we have <math|U<around*|(|\<bbb-Z\><around*|[|<sqrt|-d>|]>|)>=<around*|{|-1,1|}>>
  since certainly 1 and \<minus\>1 are units, and if <math|z+w<sqrt|-d>> is a
  unit then taking absolute values as above we get <math|x,y\<in\>\<bbb-Z\>>
  such that <math|<around*|(|z<rsup|2>+d w<rsup|2>|)><around*|(|x<rsup|2>+d
  y<rsup|2>|)>=1>; since <math|d\<gtr\>1> we get <math|w=0> and
  <math|z\<in\><around*|{|-1,1|}>> as required.

  <\example>
    Given a ring <math|R> we write <math|Z<around*|(|R|)>> for the
    <strong|centre> of <math|R>, that is the set of <math|x\<in\>R> that
    commute with all other elements of <math|R> <em|i.e.> such that
    <math|x*y=y*x> for all <math|y\<in\>R>.

    The centre is a subring by the subring test: <math|1*x=x=x*1> for all
    <math|x\<in\>R>, so <math|1\<in\>Z<around*|(|R|)>>. Secondly, for
    <math|x,x<rprime|'>\<in\>Z<around*|(|R|)>>, and <math|y\<in\>R> we have
    <math|<around*|(|x-x<rprime|'>|)>y=x*y+<around*|(|-x<rprime|'>|)>y=x*y+x<rprime|'><around*|(|-y|)>=y*x+<around*|(|-y|)>x<rprime|'>=y*x+y<around*|(|-x<rprime|'>|)>=y<around*|(|x-x<rprime|'>|)>>
    and <math|<around*|(|x*x<rprime|'>|)>y=x<around*|(|x<rprime|'>*y|)>=x<around*|(|y*x<rprime|'>|)>=<around*|(|x*y|)>x<rprime|'>=<around*|(|y*x|)>x<rprime|'>=y<around*|(|x*x<rprime|'>|)>>.
  </example>

  <\example>
    The ring of integers has no proper subrings, since any such subring must
    contain 1 and so by induction <math|\<bbb-N\><rsup|\<ast\>>> and hence
    <math|\<bbb-N\><rsup|\<ast\>>-\<bbb-N\><rsup|\<ast\>>=\<bbb-Z\>>.

    <with|font|Segoe UI Emoji|\<#26A0\>>The set
    <math|\<bbb-N\><rsup|\<ast\>>> contains 1 and if
    <math|x,y\<in\>\<bbb-N\><rsup|\<ast\>>> then
    <math|x+y,x*y\<in\>\<bbb-N\><rsup|\<ast\>>>, but
    <math|\<bbb-N\><rsup|\<ast\>>> is <em|not> a subring of <math|\<bbb-Z\>>
    because it does not contain 0. It follows that <math|x-y> may not be
    replaced by <math|x+y> in the hypotheses of the subring test.
  </example>

  <\observation>
    For <math|\<phi\>:R\<rightarrow\>S> a ring homomorphism, <math|Im
    \<phi\>> is a subring of <math|S> by the subring test:
    <math|1<rsub|S>=\<phi\><around*|(|1<rsub|R>|)>\<in\>Im \<phi\>>; and if
    <math|x,y\<in\>Im \<phi\>> then there are <math|z,w\<in\>R> such that
    <math|x=\<phi\><around*|(|z|)>> and <math|y=\<phi\><around*|(|w|)>> so
    <math|x*y=\<phi\><around*|(|z*w|)>\<in\>Im \<phi\>> and
    <math|x-y=\<phi\><around*|(|x|)>-\<phi\><around*|(|y|)>=\<phi\><around*|(|x-y|)>\<in\>Im
    \<phi\>>.
  </observation>

  <subsection|Fields>

  We say that a commutative ring <math|R> is a <strong|field> if
  <math|U<around*|(|R|)>=R<rsup|\<ast\>>>. A subring that is also a field is
  called a <strong|subfield>. Throughout these notes <math|\<bbb-F\>> always
  denotes a field.

  <\example>
    The complex numbers <math|\<bbb-C\>> are a field with <math|\<bbb-R\>> as
    a subfield.
  </example>

  <\proposition>
    Suppose that <math|\<phi\>:\<bbb-F\>\<rightarrow\>R> is a ring
    homomorphism and <math|R> is non-trivial. Then <math|\<phi\>> is an
    injection and <math|Im \<phi\>> is a subfield of <math|R>.
  </proposition>

  <\proof>
    If <math|\<phi\><around*|(|x|)>=\<phi\><around*|(|y|)>> and
    <math|x\<neq\>y> then <math|x-y\<in\>\<bbb-F\><rsup|\<ast\>>> and so
    there is <math|u> such that <math|<around*|(|x-y|)>u=1> whence
    <math|0=0*\<phi\><around*|(|u|)>=<around*|(|\<phi\><around*|(|x|)>-\<phi\><around*|(|y|)>|)>\<phi\><around*|(|u|)>=\<phi\><around*|(|<around*|(|x-y|)>u|)>=\<phi\><around*|(|1|)>=1>,
    which contradicts the non-triviality of <math|R>.

    <math|Im \<phi\>> is a subring of <math|R> which is non-trivial since
    <math|R> is non-trivial, and it is commutative since
    <math|\<phi\><around*|(|x|)>\<phi\><around*|(|y|)>=\<phi\><around*|(|x
    y|)>=\<phi\><around*|(|y x|)>=\<phi\><around*|(|y|)>\<phi\><around*|(|x|)>>.
    If <math|\<phi\><around*|(|y|)>\<neq\>0> then since
    <math|\<phi\><around*|(|0|)>=0> and <math|\<phi\>> is an injection,
    <math|y\<neq\>0> and so <math|y<rsup|-1>> exists and
    <math|\<phi\><around*|(|y|)>\<phi\><around*|(|y<rsup|-1>|)>=\<phi\><around*|(|1|)>=1>,
    whence <math|\<phi\><around*|(|y|)>> is a unit and <math|Im \<phi\>> is a
    subfield.
  </proof>

  <\warning*>
    A subfield doesn't have to be contained in a field.
  </warning*>

  <\proposition>
    Suppose that <math|\<phi\>:\<bbb-F\>\<rightarrow\>R> is a ring
    homomorphism. Then the map <math|\<bbb-F\>\<times\>R\<rightarrow\>R;<around*|(|\<lambda\>,r|)>\<mapsto\>\<lambda\>.r\<assign\>\<phi\><around*|(|\<lambda\>|)>r>
    is a scalar multiplication of the field <math|\<bbb-F\>> on the additive
    group of <math|R> giving an <math|\<bbb-F\>>-vector space such that the
    right multiplication maps on <math|R> are linear, and if <math|\<phi\>>
    maps <math|\<bbb-F\>> into the centre of <math|R> then so are the left
    multiplication maps. In particular if <math|R> is commutative then the
    left and right multiplication maps are linear.

    Conversely, if <math|R> is a ring which is also an
    <math|\<bbb-F\>>-vector space in such a way that all the right
    multiplication maps are linear then the map
    <math|\<bbb-F\>\<rightarrow\>R;\<lambda\>\<mapsto\>\<lambda\>.1<rsub|R>>
    is a ring homomorphism and if all the left multiplication maps are also
    linear then its image is in the centre of <math|R>.
  </proposition>

  <\proof>
    The additive group of <math|R> is a commutative group by definition. We
    also have <math|<around*|(|\<lambda\>\<mu\>|)>.v=\<phi\><around*|(|\<lambda\>*\<mu\>|)>v=<around*|(|\<phi\><around*|(|\<lambda\>|)>\<phi\><around*|(|\<mu\>|)>|)>v=\<phi\><around*|(|\<lambda\>|)><around*|(|\<phi\><around*|(|\<mu\>|)>v|)>=\<lambda\>.<around*|(|\<mu\>.v|)>;1<rsub|\<bbb-F\>>.v=\<phi\><around*|(|1<rsub|\<bbb-F\>>|)>v=1<rsub|R>
    v=v;<around*|(|\<lambda\>+\<mu\>|)>.v=\<phi\><around*|(|\<lambda\>+\<mu\>|)>v=<around*|(|\<phi\><around*|(|\<lambda\>|)>+\<phi\><around*|(|\<mu\>|)>|)>v=\<phi\><around*|(|\<lambda\>|)>v+\<phi\><around*|(|\<mu\>|)>v=\<lambda\>.v+\<mu\>.v>;
    and <math|\<lambda\>.<around*|(|v+w|)>=\<phi\><around*|(|\<lambda\>|)><around*|(|v+w|)>=\<phi\><around*|(|\<lambda\>|)>v+\<phi\><around*|(|\<lambda\>|)>w=\<lambda\>.v+\<lambda\>.w>.
    It follows <math|R> is an <math|\<bbb-F\>>-vector space as claimed.

    Right multiplication by <math|r> is linear since it is a group
    homomorphism and <math|\<lambda\>.<around*|(|v*r|)>=\<phi\><around*|(|\<lambda\>|)><around*|(|v*r|)>=<around*|(|\<phi\><around*|(|\<lambda\>|)>v|)>r=<around*|(|\<lambda\>.v|)>r>.
    Finally, left multiplication by <math|r> is a group homomorphism, and if
    it commutes with all elements of the image of <math|\<phi\>> (which is
    certainly true if <math|\<phi\>> maps to the centre of <math|R>), then
    <math|\<lambda\>.<around*|(|r*v|)>=\<phi\><around*|(|\<lambda\>|)><around*|(|r
    v|)>=<around*|(|\<phi\><around*|(|\<lambda\>|)>r|)>v=<around*|(|r*\<phi\><around*|(|\<lambda\>|)>|)>v=r<around*|(|\<phi\><around*|(|\<lambda\>|)>v|)>=r<around*|(|\<lambda\>.v|)>>,
    and so left multiplication by <math|r> is linear.

    Conversely, write <math|\<phi\>> for the given map then
    <math|\<phi\><around*|(|1<rsub|\<bbb-F\>>|)>=1<rsub|\<bbb-F\>>.1<rsub|R>=1<rsub|R>;\<phi\><around*|(|x+y|)>=<around*|(|x+y|)>.1<rsub|R>=x.1<rsub|R>+y.1<rsub|R>=\<phi\><around*|(|x|)>+\<phi\><around*|(|y|)>>;
    and <math|\<phi\><around*|(|x*y|)>=<around*|(|x*y|)>.1<rsub|R>=x.<around*|(|y.1<rsub|R>|)>=x.\<phi\><around*|(|y|)>=x.<around*|(|1<rsub|R>*\<phi\><around*|(|y|)>|)>=<around*|(|x.1<rsub|R>|)>\<phi\><around*|(|y|)>=\<phi\><around*|(|x|)>\<phi\><around*|(|y|)>>
    since the map <math|R\<rightarrow\>R;z\<mapsto\>z*\<phi\><around*|(|y|)>>
    is linear. It follows that <math|\<phi\>> is a ring homomorphism as
    claimed. If all left multiplication maps are linear then for
    <math|r\<in\>R> we have <math|r*\<phi\><around*|(|\<lambda\>|)>=r<around*|(|\<lambda\>.1<rsub|R>|)>=\<lambda\>.<around*|(|r*1<rsub|R>|)>=\<lambda\>.<around*|(|1<rsub|R>*r|)>=<around*|(|\<lambda\>.1<rsub|R>|)>r=\<phi\><around*|(|\<lambda\>|)>r>
    and so <math|\<phi\><around*|(|\<lambda\>|)>\<in\>Z<around*|(|R|)>>.
  </proof>

  We call the vector space structure of the proposition the
  <strong|<math|\<bbb-F\>>-(vector) space structure on <math|R> induced by
  <math|\<phi\>>>.

  <\example>
    The inclusion map <math|\<bbb-R\>\<rightarrow\>\<bbb-C\>> induces the
    usual <math|\<bbb-R\>>-vector space structure on the additive group of
    <math|\<bbb-C\>>. <math|<around*|{|1,i|}>> is a basis for this vector
    space, which is another way of saying that every complex number can be
    written uniquely in the form <math|a+b i> for reals <math|a> and
    <math|b>.
  </example>

  <\example>
    Complex conjugation, <math|\<bbb-C\>\<rightarrow\>\<bbb-C\>;z\<mapsto\><wide|z|\<bar\>>>
    is a ring homomorphism that is different from the identity so we have two
    different <math|\<bbb-C\>>-vector space structures on the additive group
    of <math|\<bbb-C\>>: one has scalar multiplication
    <math|\<lambda\>.z\<assign\>\<lambda\>*z> and the other
    <math|\<lambda\>.z\<assign\><wide|\<lambda\>|\<bar\>>*z> for all
    <math|\<lambda\>,z\<in\>\<bbb-C\>>. <hlink|smallest rigid extension field
    of the complex numbers|https://mathoverflow.net/questions/61058/>
  </example>

  <subsection|Zero divisors and integral domains>

  In a ring <math|R> we call <math|y\<in\>R> a <strong|left> (resp.
  <strong|right>) <strong|zero-divisor> if the left (resp. right)
  multiplication-by-<math|y> map has a non-trivial kernel <em|i.e.> if there
  is some <math|x\<neq\>0> such that <math|y*x=0> (resp. <math|x*y=0>). A
  non-trivial commutative ring <math|R> is an <strong|integral domain> if it
  has no non-zero zero-divisors.

  <\example>
    <math|\<bbb-Z\>> is an integral domain \U it is our prototypical example.
  </example>

  <\observation>
    If <math|x\<in\>U<around*|(|R|)>> then <math|x> is not a left (resp.
    right) zero-divisor since if <math|x*y=0> (resp. <math|y*x=0>) then
    <math|0=x<rsup|-1>*0=x<rsup|-1><around*|(|x*y|)>=1*y=y> (resp.
    <math|0=0*x<rsup|-1>=<around*|(|y*x|)>x<rsup|-1>=y*1=y>).
  </observation>

  <\example>
    Every field <math|\<bbb-F\>> is an integral domain since it is certainly
    a non-trivial commutative ring and every non-zero element is a unit and
    so not a zero-divisor.
  </example>

  <\example>
    <dueto|Example 1.13, contd.>By Bezout's Lemma if
    <math|gcd<around*|(|a,N|)>=1> then there are
    <math|\<alpha\>,\<beta\>\<in\>\<bbb-Z\>> such that
    <math|\<alpha\>*a+\<beta\>*N=1> and so <math|\<alpha\>*a\<equiv\>1<pmod|
    N>>. Since <math|\<bbb-Z\><rsub|N>> is commutative it follows that
    <math|a*\<alpha\>\<equiv\>1<pmod|N>> and so <math|a> is a unit in
    <math|\<bbb-Z\><rsub|N>>. On the other hand, if
    <math|gcd<around*|(|a,N|)>\<gtr\>1> then
    <math|a\<times\><frac|N|gcd<around*|(|a,N|)>>\<equiv\>0<around*|(|mod
    N|)>> and <math|<frac|N|gcd<around*|(|a,N|)>>\<nequiv\>0<around*|(|mod
    N|)>>, so <math|a> is a zero-divisor and hence not a unit. It follows
    that <math|U<around*|(|\<bbb-Z\><rsub|N>|)>=<around*|{|a<around*|(|mod
    N|)>:gcd<around*|(|a,N|)>=1|}>>.

    If <math|p\<gtr\>1> is prime then for all <math|a>, either
    <math|p\<divides\>a> or <math|gcd<around*|(|a,p|)>=1>. Hence
    <math|U<around*|(|\<bbb-Z\><rsub|p>|)>=\<bbb-Z\><rsup|\<ast\>><rsub|p>>
    and so <math|\<bbb-Z\><rsub|p>> is a field; we denote it
    <math|\<bbb-F\><rsub|p>> to emphasise this fact.

    If <math|N\<gtr\>1> is composite, say <math|N=a*b> for <math|a,b\<gtr\>1>
    then <math|a*b\<equiv\>0<pmod|N>> but <math|a,b\<nequiv\>0<pmod|N>> and
    so <math|\<bbb-Z\><rsub|N>> is not even an integral domain.

    If <math|N=1> then <math|\<bbb-Z\><rsub|N>> is trivial, and so not even
    non-trivial!
  </example>

  <\observation>
    If <math|R> is an integral domain and <math|S> is a subring of <math|R>
    then <math|S> is an integral domain: <math|S> is certainly non-trivial
    and commutative since <math|R> is, and for <math|y\<in\>S>, the
    multiplication-by-<math|y> map on <math|S> is the restriction of the
    multiplication-by-<math|y> map on <math|R>, and so if the kernel of the
    latter is trivial then so is the kernel of the former.
  </observation>

  <\example>
    For <math|d\<in\>\<bbb-N\><rsup|\<ast\>>>, the ring
    <math|\<bbb-Z\><around*|[|<sqrt|-d>|]>>, and in particular the Gaussian
    integers, is a subring of <math|\<bbb-C\>> and so an integral domain.
  </example>

  <\example>
    The algebraic integers, denoted <math|<wide|\<bbb-Z\>|\<wide-bar\>>>, are
    the complex numbers <math|\<alpha\>> for which there is
    <math|d\<in\>\<bbb-N\><rsup|\<ast\>>> and
    <math|a<rsub|d-1>,\<ldots\>,a<rsub|0>\<in\>\<bbb-Z\>> such that
    <math|\<alpha\><rsup|d>+a<rsub|d-1>\<alpha\><rsup|d-1>+\<cdots\>+a<rsub|1>\<alpha\>+a<rsub|0>=0>.
    We shall make use of arguments from the modules part of the course to
    show that <math|<wide|\<bbb-Z\>|\<wide-bar\>>> is a subring of
    <math|\<bbb-C\>>, and given this we conclude
    <math|<wide|\<bbb-Z\>|\<wide-bar\>>> is an integral domain.

    <math|<wide|\<bbb-Z\>|\<wide-bar\>>> is not a field since
    <math|<frac|1|2>\<nin\><wide|\<bbb-Z\>|\<wide-bar\>>>, because if it were
    then there would be <math|a<rsub|d-1>,\<ldots\>,a<rsub|0>\<in\>\<bbb-Z\>>
    such that <math|1+2<around*|(|a<rsub|d-1>+\<cdots\>+a<rsub|0>2<rsup|d-1>|)>=0>;
    a contradiction.
  </example>

  <\proposition>
    Suppose that <math|R> is a ring with no non-zero zero divisors that is
    also a finite dimensional vector space in such a way that left and right
    multiplication maps are linear. Then <math|U<around*|(|R|)>=R<rsup|\<ast\>>>,
    and in particular if <math|R> is an integral domain then <math|R> is a
    field.
  </proposition>

  <\proof>
    For <math|a\<in\>R> the map <math|R\<rightarrow\>R;x\<mapsto\>x*a> is
    linear, and since <math|R> is an integral domain it is injective if
    <math|a\<in\>R<rsup|\<ast\>>>. Since <math|R> is finite dimensional the
    Rank-Nullity Theorem tells us that the map is surjective, and hence there
    is <math|x\<in\>R> such that <math|x a=1>. Similarly there is <math|y>
    such that <math|a*y=1>, and finally <math|x=x*1=x<around*|(|a*y|)>=<around*|(|x*a|)>y=1*y=y>
    so <math|a\<in\>U<around*|(|R|)>> as required.
  </proof>

  <subsection|Product of rings>

  For rings <math|R<rsub|1>,\<ldots\>,R<rsub|n>> the product group
  <math|R<rsub|1>\<times\>\<cdots\>\<times\>R<rsub|n>> of the additive groups
  of the rings <math|R<rsub|i>> may be equipped with a binary operation
  defined by <math|<around*|(|x*y|)><rsub|i>\<assign\>x<rsub|i>y<rsub|i>> for
  <math|1\<leqslant\>i\<leqslant\>n> making it into a ring with identity
  <math|1=<around*|(|1<rsub|R<rsub|1>>,\<ldots\>,1<rsub|R<rsub|n>>|)>>. This
  ring is called the <strong|direct product> of the <math|R<rsub|i>>s.

  <\observation>
    The group of units of a product ring is equal to the product group of the
    groups of units of the rings <em|i.e.>
    <math|U<around*|(|R<rsub|1>\<times\>\<cdots\>\<times\>R<rsub|n>|)>=U<around*|(|R<rsub|1>|)>\<times\>\<cdots\>\<times\>U<around*|(|R<rsub|n>|)>>.
  </observation>

  <\example>
    The maps <math|\<pi\><rsub|i>:R<rsub|1>\<times\>\<cdots\>\<times\>R<rsub|n>\<rightarrow\>R<rsub|i>;x\<mapsto\>x<rsub|i>>
    are ring homomorphisms called <strong|projection homomorphisms>.
  </example>

  <\example>
    The map <math|R\<rightarrow\>R<rsup|n>;x\<mapsto\><around*|(|x,\<ldots\>,x|)>>
    is a ring homomorphism called the <strong|diagonal homomorphism (into
    <math|R<rsup|n>>)>.

    The diagonal homomorphism <math|\<bbb-F\>\<rightarrow\>\<bbb-F\><rsup|n>>
    induces an <math|\<bbb-F\>>-vector space structure on
    <math|\<bbb-F\><rsup|n>> which is the usual <math|\<bbb-F\>>-vector space
    structure on <math|\<bbb-F\><rsup|n>> <em|i.e.> having scalar
    multiplication <math|\<lambda\>.v=<around*|(|\<lambda\>v<rsub|1>,\<ldots\>,\<lambda\>v<rsub|n>|)>>
    for <math|\<lambda\>\<in\>\<bbb-F\>> and <math|v\<in\>\<bbb-F\><rsup|n>>.
    <with|font|Segoe UI Emoji|\<#26A0\>>The ring <math|\<bbb-F\><rsup|n>> has
    more structure than the vector space <math|\<bbb-F\><rsup|n>> because the
    former comes with a multiplication.
  </example>

  <\example>
    For <math|R> a ring, <math|R<rsup|2>> is never an integral domain: if
    <math|R> is trivial then <math|1<rsub|R<rsup|2>>=<around*|(|1<rsub|R>,1<rsub|R>|)>=<around*|(|0<rsub|R>,0<rsub|R>|)>=0<rsub|R<rsup|2>>>,
    so <math|R<rsup|2>> is trivial. Otherwise
    <math|<around*|(|0<rsub|R>,1<rsub|R>|)><around*|(|1<rsub|R>,0<rsub|R>|)>=<around*|(|0<rsub|R>,0<rsub|R>|)>=0<rsub|R<rsup|2>>>,
    <math|<around*|(|0<rsub|R>,1<rsub|R>|)>,<around*|(|1<rsub|R>,0<rsub|R>|)>\<in\><around*|(|R<rsup|2>|)><rsup|\<ast\>>>
    and so these are non-zero zero-divisors.
  </example>

  <subsection|Prototypical rings>

  Groups of symmetries are the prototypes for abstract groups and rings have
  a similar prototype in which the underlying set is replaced by a
  commutative group.

  <\proposition>
    Suppose that <math|M> and <math|N> are commutative groups with binary
    operations <math|+<rsub|M>> and <math|+<rsub|N>>, and identities
    <math|0<rsub|M>> and <math|0<rsub|N>> respectively. Then <math|Hom(M,N)>,
    the set of group homomorphisms <math|M\<rightarrow\>N>, is itself a
    commutative group under + defined pointwise on <math|Hom(M,N)> by

    <\equation*>
      <around|(|\<phi\>+\<psi\>|)><around|(|x|)>\<assign\>\<phi\><around|(|x|)>+<rsub|N>*\<psi\><around|(|x|)>*<text|for
      all >x\<in\>M,
    </equation*>

    with identity <math|z:M\<rightarrow\>N;x\<mapsto\>0<rsub|N>>, and the
    inverse of <math|\<phi\>> is the pointwise negation, meaning for all
    <math|x\<in\>M>, <math|(\<minus\>\<phi\>)(x)> is the inverse of
    <math|\<phi\>(x)> in <math|N>.
  </proposition>

  <\proof>
    Suppose that <math|\<phi\>,\<psi\>\<in\>Hom<around*|(|M,N|)>>. Then for
    all <math|x,y\<in\>M> we have

    <\align*>
      <tformat|<table|<row|<cell|<around|(|\<phi\>+\<psi\>|)>*<around|(|x+<rsub|M>y|)>>|<cell|=\<phi\>*<around|(|x+<rsub|M>y|)>+<rsub|N>\<psi\>*<around|(|x+<rsub|M>y|)>>|<cell|>>|<row|<cell|>|<cell|=<around|(|\<phi\><around|(|x|)>+<rsub|N>\<phi\><around|(|y|)>|)>+<rsub|N><around|(|\<psi\><around|(|x|)>+<rsub|N>\<psi\><around|(|y|)>|)>>|<cell|<small|\<phi\>*<text|and
      >\<psi\><text| are group homomorphisms>>>>|<row|<cell|>|<cell|=<around|(|\<phi\><around|(|x|)>+<rsub|N>\<psi\><around|(|x|)>|)>+<rsub|N><around|(|\<phi\><around|(|y|)>+<rsub|N>\<psi\><around|(|y|)>|)>>|<cell|<small|<text|associativity
      and commutativity of >+<rsub|N>>>>|<row|<cell|>|<cell|=<around|(|\<phi\>+\<psi\>|)><around|(|x|)>+<rsub|N><around|(|\<phi\>+\<psi\>|)><around|(|y|)>>|<cell|<small|<text|definition
      of pointwise addition>>>>>>
    </align*>

    It follows that <math|\<phi\>+\<psi\>\<in\>Hom<around|(|M,N|)>>.
    Pointwise addition is commutative and associative because addition on
    <math|N> is commutative and associative. The map <math|z> is a
    homomorphism because <math|z<around|(|x|)>+<rsub|N>z<around|(|y|)>=0<rsub|N>+<rsub|N>0<rsub|N>=0<rsub|N>=z*<around|(|x+<rsub|M>y|)>>,
    and it is an identity for pointwise addition because <math|0<rsub|N>> is
    an identity for <math|N>. Finally, if <math|\<phi\>\<in\>Hom(M,N)> then
    <math|\<minus\>\<phi\>\<in\>Hom(M,N)> because it is the composition of
    the homomorphism <math|\<phi\>> and negation which is a homomorphism on
    <math|N> since <math|+<rsub|N>> is commutative, and this map is an
    inverse for <math|\<phi\>(x)> under pointwise addition by design.
  </proof>

  <\remark>
    To show that <math|Hom<around|(|M,N|)>> is a closed under pointwise
    addition and negation it is essential that <math|N> be commutative.
  </remark>

  <\proposition>
    Suppose that <math|M,N,> and <math|P> are commutative groups, and
    <math|+<rsub|N>> and <math|+<rsub|P>> are the group operations on
    <math|N> and <math|Hom(M,N)>, and <math|P> and <math|Hom(N,P)>
    respectively. If <math|\<phi\>\<in\>Hom(M,N)> and
    <math|\<psi\>\<in\>Hom(N,P)>, then <math|\<psi\>\<circ\>\<phi\>\<in\>Hom(M,P)>;
    if <math|\<pi\>\<in\>Hom(M,N)> then <math|\<psi\>\<circ\>(\<phi\>+<rsub|N>\<pi\>)=(\<psi\>\<circ\>\<phi\>)+<rsub|P>(\<psi\>\<circ\>\<pi\>)>;
    and if <math|\<pi\>\<in\>Hom(N,P)> then
    <math|(\<psi\>+<rsub|P>\<pi\>)\<circ\>\<phi\>=(\<psi\>\<circ\>\<phi\>)+<rsub|P>(\<pi\>\<circ\>\<phi\>)>.
  </proposition>

  <\proof>
    The composition of homomorphisms is a homomorphism which says exactly
    that if <math|\<phi\>\<in\>Hom(M,N)> and <math|\<psi\>\<in\>Hom(N, P)>,
    then <math|\<psi\>\<circ\>\<phi\>\<in\>Hom(M,P)>. Now, if
    <math|\<phi\>,\<pi\>\<in\>Hom(M,N)> and <math|\<psi\>\<in\>Hom(N,P)>,
    then

    <\equation*>
      \<psi\>\<circ\>(\<phi\>+<rsub|N>\<pi\>)(x)=\<psi\>(\<phi\>(x)+<rsub|N>\<pi\>(x))=\<psi\>(\<phi\>(x))+<rsub|P>\<psi\>(\<pi\>(x))=((\<psi\>\<circ\>\<phi\>)+<rsub|P>(\<psi\>\<circ\>\<pi\>))(x)
    </equation*>

    by definition and the fact that <math|\<psi\>> is a homomorphism, and we
    have that <math|\<psi\>\<circ\>(\<phi\>+<rsub|N>
    \<pi\>)=(\<psi\>\<circ\>\<phi\>)+<rsub|P>(\<psi\>\<circ\>\<pi\>)> as
    claimed. On the other hand, if <math|\<phi\>\<in\>Hom(M,N)> and
    <math|\<psi\>,\<pi\>\<in\>Hom(N,P)>, then

    <\equation*>
      (\<psi\>+<rsub|P> \<pi\>)\<circ\>\<phi\>(x)=\<psi\>(\<phi\>(x))+<rsub|P>\<pi\>(\<phi\>(x))=((\<psi\>\<circ\>\<phi\>)+<rsub|P>(\<pi\>\<circ\>\<phi\>))(x)
    </equation*>

    by definition. The result is proved.
  </proof>

  <\remark>
    For the identity <math|\<psi\>\<circ\>(\<phi\>+<rsub|N>\<pi\>)=(\<psi\>\<circ\>\<phi\>)+<rsub|P>(\<psi\>\<circ\>\<pi\>)>
    we used the homomorphism property of <math|\<psi\>>, while the identity
    <math|(\<psi\>+<rsub|P>\<pi\>)\<circ\>\<phi\>=(\<psi\>\<circ\>\<phi\>)+<rsub|P>(\<pi\>\<circ\>\<phi\>)>
    followed simply from the definition; <em|c.f.> Exercise I.1.
  </remark>

  <\theorem>
    Suppose that <math|M> is a commutative group. Then the set
    <math|Hom<around*|(|M,M|)>> equipped with pointwise addition as its
    addition and functional composition as its multiplication is a ring whose
    zero is the map <math|M\<rightarrow\>M;x\<mapsto\>0<rsub|M>> and whose
    multiplicative identity is the map <math|M\<rightarrow\>M;x\<mapsto\>x>.
  </theorem>

  <\proof>
    <math|Hom<around*|(|M,M|)>> is a commutative group with the given
    identity under this addition, and by the second part the proposed
    multiplication distributes over this addition. It remains to note that
    composition of functions is associative so the proposed multiplication is
    associative, and the map <math|M\<rightarrow\>M;x\<mapsto\>x> is
    certainly a homomorphism and an identity for composition.
  </proof>

  <subsection|Matrix rings>

  Given a ring <math|R>, we write <math|M<rsub|n,m><around*|(|R|)>> for the
  set of <math|n\<times\>m> matrices with entries in <math|R>, and
  <math|M<rsub|n><around*|(|R|)>\<assign\>M<rsub|n,n><around*|(|R|)>>. For
  <math|A,A<rprime|'>\<in\>M<rsub|n,m><around*|(|R|)>> and
  <math|B\<in\>M<rsub|m,p>(R)> we define matrices
  <math|A+A<rprime|'>\<in\>M<rsub|n,m><around*|(|R|)>> and
  <math|A*B\<in\>M<rsub|n,p>(R)> by

  <\equation>
    (A+A<rprime|'>)<rsub|i,j>\<assign\>A<rsub|i,j>+B<rsub|i,j><text| and
    ><around*|(|A*B|)><rsub|i,k>\<assign\><big|sum><rsub|j=1><rsup|m>A<rsub|i,j>B<rsub|j,k>
  </equation>

  We write <math|0<rsub|n\<times\>m>> for the matrix in
  <math|M<rsub|n,m><around*|(|R|)>> with <math|0<rsub|R>> in every entry, and
  <math|I<rsub|n>> for the <math|n\<times\>n> matrix with <math|1<rsub|R>>s
  on the diagonal and <math|0<rsub|R>>s elsewhere.

  <\proposition>
    <dueto|Algebra of matrices>Suppose that <math|R> is a ring. Then
    <math|M<rsub|n,m><around*|(|R|)>> is a commutative group under + with
    identity <math|0<rsub|n\<times\>m>> and for which the inverse of
    <math|A\<in\>M<rsub|n,m>(R)> is the matrix <math|\<minus\>A> with
    <math|(\<minus\>A)<rsub|i,j>=\<minus\>A<rsub|i,j>>. Furthermore, if
    <math|><math|A\<in\>M<rsub|n,m><around*|(|R|)>,B,B<rprime|'>\<in\>M<rsub|n,m><around*|(|R|)>>,
    and <math|C,C<rprime|'>\<in\>M<rsub|p,n>(R)> then
    <math|C(A*B)=(C*A)B,A(B+B<rprime|'>)=(A*B)+(A*B<rprime|'>),(C+C<rprime|'>)A=(C*A)+(C<rprime|'>A),A*I<rsub|m>=A>
    and <math|I<rsub|n>A=A>.
  </proposition>

  <\remark>
    We omit the proof. One can proceed directly using a change of variables
    and distributivity, or using some of the language of modules.
  </remark>

  The commutative group <math|M<rsub|n><around*|(|R|)>> with multiplication
  <math|M<rsub|n>(R)\<times\>M<rsub|n><around*|(|R|)>\<rightarrow\>M<rsub|n><around*|(|R|)>;(A,
  B)\<mapsto\>A*B> is a ring with multiplicative identity <math|I<rsub|n>> as
  a result of the algebra of matrices. A <strong|matrix ring> is a subring of
  <math|M<rsub|n><around*|(|R|)>>.

  <\remark>
    For <math|A\<in\>M<rsub|n><around*|(|R|)>> the <strong|determinant> of
    <math|A> is defined to be

    <\equation*>
      det A\<assign\><big|sum><rsub|\<sigma\>\<in\>S<rsub|n>>sign(\<sigma\>)A<rsub|1,\<sigma\>(1)>\<cdots\>A<rsub|n,\<sigma\>(n)>
    </equation*>

    where <math|S<rsub|n>> is the symmetry group of permutations of
    <math|{1,\<ldots\>,n}>, and <math|sign(\<sigma\>)> is the sign of the
    permutation <math|\<sigma\>>.

    We shall see in the second half of the course that for <math|R>
    commutative, <math|A\<in\>U(M<rsub|n><around*|(|R|)>)> if and only if
    <math|det A\<in\>U(R)>, generalising what we already know for fields
    since <math|det A\<in\>U(\<bbb-F\>)> if and only if <math|det
    A\<neq\>0<rsub|\<bbb-F\>>>. <math|U(M<rsub|n><around*|(|\<bbb-F\>|)>)=GL<rsub|n><around*|(|\<bbb-F\>|)>>
    is a field. For non-commutative rings Exercise I.5 gives an example to
    show that this equivalence can fail.
  </remark>

  <\example>
    For <math|R> non-trivial the ring <math|M<rsub|2>(R)> is not commutative:

    <\equation*>
      <around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|2|2|cell-rborder|0ln>|<table|<row|<cell|1>|<cell|1>>|<row|<cell|0>|<cell|1>>>>>|)><around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|2|2|cell-rborder|0ln>|<table|<row|<cell|1>|<cell|0>>|<row|<cell|1>|<cell|1>>>>>|)>=<around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|2|2|cell-rborder|0ln>|<table|<row|<cell|2>|<cell|1>>|<row|<cell|1>|<cell|1>>>>>|)>\<neq\><around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|2|2|cell-rborder|0ln>|<table|<row|<cell|1>|<cell|1>>|<row|<cell|1>|<cell|2>>>>>|)>=<around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|2|2|cell-rborder|0ln>|<table|<row|<cell|1>|<cell|0>>|<row|<cell|1>|<cell|1>>>>>|)><around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|2|2|cell-rborder|0ln>|<table|<row|<cell|1>|<cell|1>>|<row|<cell|0>|<cell|1>>>>>|)>
    </equation*>
  </example>

  <\example>
    Given a ring <math|R>, the map

    <\equation*>
      \<#2206\>:R\<rightarrow\>M<rsub|n><around*|(|R|)>;\<lambda\>\<mapsto\><around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|3|3|cell-halign|c>|<cwith|1|-1|4|4|cell-halign|c>|<cwith|1|-1|4|4|cell-rborder|0ln>|<table|<row|<cell|\<lambda\>>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|\<vdots\>>>|<row|<cell|\<vdots\>>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|0>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|\<lambda\>>>>>>|)>
    </equation*>

    is a ring homomorphism called the <strong|diagonal homomorphism (into
    <math|M<rsub|n><around*|(|R|)>>)>.

    The diagonal homomorphism into <math|M<rsub|n><around*|(|\<bbb-F\>|)>>
    induces the usual <math|\<bbb-F\>>-vector space structure on
    <math|M<rsub|n><around*|(|\<bbb-F\>|)>> with scalar multiplication
    <math|(\<lambda\>.A)<rsub|i,j>=\<lambda\>A<rsub|i,j>>. Writing
    <math|E<rsup|<around*|(|i,j|)>>> for the matrix with
    <math|E<rsup|<around*|(|i,j|)>><rsub|i,j>=1> and
    <math|E<rsup|<around*|(|i,j|)>><rsub|k,l>=0> for
    <math|(k,l)\<neq\>(i,j)>, the set <math|{E<rsup|<around*|(|i,j|)>>:1\<leqslant\>i,j\<leqslant\>n}>
    is a basis for this vector space.
  </example>

  <\example>
    The <strong|quaternions> are the set

    <\equation*>
      \<bbb-H\>\<assign\><around*|{|<around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|2|2|cell-rborder|0ln>|<table|<row|<cell|z>|<cell|w>>|<row|<cell|-<wide|w|\<bar\>>>|<cell|<wide|z|\<bar\>>>>>>>|)>:z,w\<in\>\<bbb-C\>|}>
    </equation*>

    They form a subring of <math|M<rsub|2><around*|(|\<bbb-C\>|)>> by the
    subring test, and in particular <math|\<bbb-H\>> has zero
    <math|0<rsub|2\<times\>2>> and multiplicative identity <math|I<rsub|2>>.
    Now,

    <\equation*>
      A\<assign\><matrix|<tformat|<table|<row|<cell|z>|<cell|w>>|<row|<cell|-<wide|w|\<bar\>>>|<cell|<wide|z|\<bar\>>>>>>>\<neq\>0<rsub|2\<times\>2><text|
      \ if and only if >det A=<around*|\||z|\|><rsup|2>+<around*|\||w|\|><rsup|2>\<neq\>0
    </equation*>

    and hence if <math|A\<in\>\<bbb-H\><rsup|\<ast\>>> then the inverse of
    <math|A> in <math|M<rsub|2><around*|(|\<bbb-C\>|)>> exists and it is also
    in <math|\<bbb-H\>>. Hence <math|A\<in\>U(\<bbb-H\>)> and since
    <math|\<bbb-H\>> is non-trivial, <math|U(\<bbb-H\>)=\<bbb-H\><rsup|\<ast\>>>.
    <with|font|Segoe UI Emoji|\<#26A0\>><math|\<bbb-H\>> is not a field, or
    even an integral domain, since it is not commutative. A not-necessarily
    commutative ring in which <math|U<around*|(|R|)>=R<rsup|\<ast\>>> is
    called a <strong|division ring> or <strong|skew field>.

    Frobenius showed that if a ring is such that every non-zero element is a
    unit and it is also a vector space over <math|\<bbb-R\>> in such a way
    that left and right multiplication in the ring is linear, then the ring
    is isomorphic to either <math|\<bbb-R\>,\<bbb-C\>> or <math|\<bbb-H\>>.

    The ring homomorphism

    <\equation*>
      \<bbb-R\>\<rightarrow\>\<bbb-H\>;\<lambda\>\<mapsto\><matrix|<tformat|<table|<row|<cell|\<lambda\>>|<cell|0>>|<row|<cell|0>|<cell|\<lambda\>>>>>>
    </equation*>

    has image equal to the centre of <math|\<bbb-H\>>, and so induces a real
    vector space structure on <math|\<bbb-H\>> in which left and right
    multiplication maps are linear. The vector space if 4-dimensional and

    <\equation*>
      <around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|2|2|cell-rborder|0ln>|<table|<row|<cell|1>|<cell|0>>|<row|<cell|0>|<cell|1>>>>>|)>,<around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|2|2|cell-rborder|0ln>|<table|<row|<cell|i>|<cell|0>>|<row|<cell|0>|<cell|-i>>>>>|)>,<around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|2|2|cell-rborder|0ln>|<table|<row|<cell|0>|<cell|1>>|<row|<cell|-1>|<cell|0>>>>>|)><text|,
      and ><around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|2|2|cell-rborder|0ln>|<table|<row|<cell|0>|<cell|i>>|<row|<cell|i>|<cell|0>>>>>|)>
    </equation*>

    form a basis. <math|A>s element of the group <math|U(\<bbb-H\>)>, these
    generate an 8 element subgroup called the <strong|quaternion group> and
    denoted <math|Q<rsub|8>>.

    There is another natural ring homomorphism: the map

    <\equation*>
      \<bbb-C\>\<rightarrow\>\<bbb-H\>;\<lambda\>\<mapsto\><matrix|<tformat|<table|<row|<cell|\<lambda\>>|<cell|0>>|<row|<cell|0>|<cell|<wide|\<lambda\>|\<bar\>>>>>>>
    </equation*>

    which induces a 2-dimensional <math|\<bbb-C\>>-vector space structure on
    <math|\<bbb-H\>> in which right multiplication maps are linear, but left
    multiplication maps are not (in general).

    In fact there is no <math|\<bbb-C\>>-vector space structure on
    <math|\<bbb-H\>> such that all left and right multiplication maps are
    linear: If there were it would give rise to a ring homomorphism
    <math|\<bbb-C\>\<rightarrow\>\<bbb-H\>> mapping into the centre of
    <math|\<bbb-H\>>. The centre of <math|\<bbb-H\>> is isomorphic to
    <math|\<bbb-R\>>, and hence we could have a ring homomorphism
    <math|\<bbb-C\>\<rightarrow\>\<bbb-R\>> which we see in Exercise I.3 is
    not possible. <with|font|Segoe UI Emoji|\<#26A0\>>In particular,
    <math|\<bbb-H\>> is <em|not> a subspace of the usual
    <math|\<bbb-C\>>-vector space <math|M<rsub|2>(\<bbb-C\>)> as defined in
    Example 1.47 because in that structure left and right multiplication
    <em|are> linear, and since <math|\<bbb-H\>> is a subring it were also
    subspace they would restrict to be linear on <math|\<bbb-H\>>.
  </example>

  <subsection|Polynomial rings>

  <\proposition>
    <dueto|Algebra of polynomials>Suppose that <math|R> is a subring of
    <math|S>, <math|\<lambda\>\<in\>S> commutes with all elements of
    <math|R>, and <math|a<rsub|0>, a<rsub|1>,\<ldots\>,b<rsub|0>,b<rsub|1>,\<ldots\>\<in\>R>
    have <math|a<rsub|i>=0> for all <math|i\<gtr\>n> and <math|b<rsub|j>=0>
    for all <math|j\<gtr\>m>. Then

    <\equation*>
      <around*|(|<big|sum><rsub|i=0><rsup|n>a<rsub|i>*\<lambda\><rsup|i>|)>+<around*|(|<big|sum><rsub|j=0><rsup|m>b<rsub|j>*\<lambda\><rsup|j>|)>=<big|sum><rsub|i=0><rsup|max
      <around|{|n,m|}>><around*|(|a<rsub|i>+b<rsub|i>|)>*\<lambda\><rsup|i><space|1em><text|and><space|1em>-<around*|(|<big|sum><rsub|i=0><rsup|n>a<rsub|i>*\<lambda\><rsup|i>|)>=<big|sum><rsub|i=0><rsup|n><around*|(|-a<rsub|i>|)>*\<lambda\><rsup|i>
    </equation*>

    and

    <\equation*>
      <around*|(|<big|sum><rsub|i=0><rsup|n>a<rsub|i>*\<lambda\><rsup|i>|)><around*|(|<big|sum><rsub|j=0><rsup|m>b<rsub|j>*\<lambda\><rsup|j>|)>=<big|sum><rsub|k=0><rsup|n+m><around*|(|<big|sum><rsub|j=0><rsup|k>a<rsub|k-j>*b<rsub|j>|)>*\<lambda\><rsup|k>
    </equation*>
  </proposition>

  <\remark>
    We omit the proof though it is not difficult: it makes essential use of
    distributivity and changes of variables.
  </remark>

  For a non-trivial ring <math|R> there is a non-trivial ring
  <math|R<around*|[|X|]>> called the <strong|polynomial ring over <math|R>
  with variable <math|X>> with <math|R> as a subring, and a distinguished
  element <math|X\<in\>R<around*|[|X|]>> which commutes with all elements of
  <math|R<around*|[|X|]>>, <em|i.e.> <math|p X=X p> for all
  <math|p\<in\>R<around*|[|X|]>>, such that

  <\equation>
    R[X]={a<rsub|0>+a<rsub|1>X+\<cdots\>+a<rsub|n>X<rsup|n>:n\<in\>\<bbb-N\><rsub|0>,a<rsub|0>,\<ldots\>,a<rsub|n>\<in\>R}
  </equation>

  and

  <\equation>
    a<rsub|0>+a<rsub|1>X+\<cdots\>+a<rsub|n>X<rsup|n>=0<rsub|R>\<Rightarrow\>a<rsub|0>,\<ldots\>,a<rsub|n>=0<rsub|R>
  </equation>

  <\remark>
    We omit the proof that such a ring exists, but the idea is to take the
    additive group of functions <math|\<bbb-N\><rsub|0>\<rightarrow\>R> with
    a finite number of non-zero entries and group operation coordinate-wise
    addition, and identify <math|X<rsup|n>> with the function taking <math|m>
    to <math|0<rsub|R>> if <math|m\<neq\>n> and <math|1<rsub|R>> if
    <math|m=n>.
  </remark>

  For more variables we define <math|R[X<rsub|1>,\<ldots\>,X<rsub|n>]\<assign\>R[X<rsub|1>,\<ldots\>,X<rsub|n-1>][X<rsub|n>]>
  and call it the <strong|polynomial ring over <math|R> in the variables
  <math|X<rsub|1>,\<ldots\>,X<rsub|n>>>.

  The algebra of polynomials and (1.3) allows the <strong|equating of
  coefficients>, meaning that if <math|a<rsub|0>+a<rsub|1>X+\<cdots\>+a<rsub|n>X<rsup|n>=b<rsub|0>+b<rsub|1>X+\<cdots\>+b<rsub|m>X<rsup|m>>
  for <math|a<rsub|0>,a<rsub|1>,\<ldots\>,b<rsub|0>,b<rsub|1>,\<ldots\>\<in\>R>
  with <math|a<rsub|i>=0> for <math|i\<gtr\>n> and <math|b<rsub|j>=0> for
  <math|j\<gtr\>m>, then <math|a<rsub|i>=b<rsub|i>> for all <math|i>.

  If <math|p\<in\>R[X]<rsup|\<ast\>>> then there is a minimal
  <math|d\<in\>\<bbb-N\><rsub|0>> and unique elements
  <math|a<rsub|0>,a<rsub|1>,\<ldots\>,a<rsub|d>\<in\>R> with
  <math|a<rsub|d>\<neq\>0<rsub|R>> such that
  <math|p(X)=a<rsub|0>+a<rsub|1>X+\<cdots\>+a<rsub|d>X<rsup|d>>. We call this
  minimal <math|d> the <strong|degree> of <math|p> and denote it <math|deg
  p>; we call <math|a<rsub|i>> the <strong|coefficient> of <math|X<rsup|i>>;
  <math|a<rsub|d>> the <strong|lead coefficient> and <math|a<rsub|0>> the
  <strong|constant coefficient>.

  A polynomial is <strong|monic> if its lead coefficient is 1, and the
  <strong|constant polynomials> are those for which the constant coefficient
  is the only coefficient that may be non-zero.

  <\example>
    The inclusion homomorphism <math|\<bbb-F\>\<rightarrow\>\<bbb-F\>[X]>
    induces an <math|\<bbb-F\>>-vector space structure on <math|\<bbb-F\>[X]>
    in such a way that all multiplication maps are linear. In this space,
    (1.2) says exactly that <math|{1,X,X<rsup|2>,\<ldots\>}> is a spanning
    set, while (1.3) tells us it is linearly independent.
  </example>

  <\proposition>
    Suppose that <math|\<phi\>:R\<rightarrow\>S> is a ring homomorphism from
    a non-trivial ring, and <math|\<lambda\>\<in\>S> commutes with all
    elements of the image of <math|\<phi\>>. Then there is a unique ring
    homomorphism <math|R<around*|[|X|]>\<rightarrow\>S> extending
    <math|\<phi\>> and mapping <math|X> to <math|\<lambda\>>, and we have

    <\equation*>
      a<rsub|0>+a<rsub|1>X+\<cdots\>+a<rsub|d>X<rsup|d>\<mapsto\>\<phi\>(a<rsub|0>)+\<phi\>(a<rsub|1>)\<lambda\>+\<cdots\>+\<phi\>(a<rsub|d>)\<lambda\><rsup|d>.
    </equation*>
  </proposition>

  <\proof>
    The proposed map is well-defined because we can equate coefficients. It
    extends <math|\<phi\>> since the constant polynomial <math|r> is mapped
    to <math|\<phi\>(r)>, and it certainly maps <math|X> to
    <math|\<lambda\>>. Finally, it is additive and multiplicative by the
    algebra of polynomials, and certainly maps 1 to 1 since it extends
    <math|\<phi\>>, and <math|\<phi\>> maps 1 to 1. It follows that the given
    map is a ring homomorphism.

    Any other ring homomorphism <math|\<phi\>> with
    <math|\<phi\><around*|(|r|)>=r> for all <math|r\<in\>R>, and
    <math|\<phi\><around*|(|X|)>=\<lambda\>> must agree with the given map on
    <math|R[X]> by the homomorphism property of <math|\<psi\>>, and hence
    uniqueness follows.
  </proof>

  We call the homomorphism of this proposition the <strong|evaluation
  homomorphism at <math|\<lambda\>> extending <math|\<phi\>>> and write
  <math|p(\<lambda\>)> for the image of <math|p> under this map.
  <with|font|Segoe UI Emoji|\<#26A0\>>The notation <math|p(\<lambda\>)> does
  not make explicit reference to <math|\<phi\>>.

  For <math|R> a subring of <math|S> and <math|\<lambda\>\<in\>S> commuting
  with all elements of <math|R>, the image of the evaluation homomorphism at
  <math|\<lambda\>> extending the inclusion homomorphism
  <math|R\<rightarrow\>S> is denoted <math|R[\<lambda\>]> and is a subring of
  <math|S>.

  <\remark>
    This proposition for polynomial rings should be compared with Theorem
    1.11 for the integers.
  </remark>

  We say that <math|\<alpha\>> is a <strong|root> of <math|p> if
  <math|p<around*|(|\<alpha\>|)>=0>.

  <\theorem>
    <dueto|Factor Theorem>Suppose <math|R> is a non-trivial ring and
    <math|\<alpha\>> is a root of <math|p>. Then there is
    <math|q\<in\>R<around*|[|X|]>> such that
    <math|p<around*|(|X|)>=q<around*|(|X|)><around*|(|X-\<alpha\>|)>>.
  </theorem>

  <\proof>
    Write <math|p(X)=a<rsub|0>+a<rsub|1>X+\<cdots\>+a<rsub|n>X<rsup|n>> and
    note that

    <\eqnarray*>
      <tformat|<table|<row|<cell|p<around*|(|X|)>>|<cell|=>|<cell|p<around|(|X|)>-p<around|(|\<alpha\>|)>>>|<row|<cell|>|<cell|=>|<cell|<big|sum><rsub|i=0><rsup|n>a<rsub|i>*<around*|(|X<rsup|i>-\<alpha\><rsup|i>|)>>>|<row|<cell|>|<cell|=>|<cell|<around*|(|<big|sum><rsub|i=0><rsup|n>a<rsub|i>*<around*|(|X<rsup|i-1>+X<rsup|i-2>*\<alpha\>+\<cdots\>+X*\<alpha\><rsup|i-2>+\<alpha\><rsup|i-1>|)>|)>*<around|(|X-\<alpha\>|)>>>>>
    </eqnarray*>

    \;
  </proof>

  Integral domains produce polynomial rings where the degree function behaves
  nicely:

  <\proposition>
    Suppose that <math|R> is a non-trivial commutative ring. Then TFAE:

    (i) <math|R> is an integral domain;

    (ii) <math|R[X]> is an integral domain;

    (iii) for every <math|p,q\<in\>R[X]<rsup|\<ast\>>> we have
    <math|p*q\<in\>R[X]<rsup|\<ast\>>> and <math|deg p*q=deg p+deg q>.
  </proposition>

  <\proof>
    Certainly (ii) implies (i) since <math|R> is a subring of <math|R[X]>,
    and (iii) implies (ii) since <math|R[X]> is a non-trivial commutative
    ring, and so the fact it is an integral domain follows by forgetting the
    degree equation in (iii).

    To see (i) implies (iii) suppose that <math|p,q\<in\>R[X]<rsup|\<ast\>>>
    have degree <math|n> and <math|m>, and lead coefficients <math|a<rsub|n>>
    and <math|b<rsub|m>> respectively. Then by the algebra of polynomials we
    see that <math|deg p*q\<leqslant\>n+m> and the coefficient of
    <math|X<rsup|n+m>> is <math|a<rsub|n>b<rsub|m>>. The coefficient of
    <math|X<rsup|n+m>> is non-zero since <math|R> is an integral domain and
    <math|a<rsub|n>,b<rsub|m>\<in\>R<rsup|\<ast\>>>. We conclude that
    <math|p*q\<in\>R[X]<rsup|\<ast\>>> and <math|deg p*q=n+m=deg p+deg q> as
    required.
  </proof>

  <\example>
    <math|\<bbb-Z\>[X]> is an integral domain since <math|\<bbb-Z\>> is an
    integral domain.
  </example>

  <\example>
    <math|\<bbb-F\>[X<rsub|1>,\<ldots\>,X<rsub|n>]> is an integral domain by
    induction on <math|n>: for the base case every field is an integral
    domain, and for the inductive step we have Proposition 1.57.
  </example>

  <\example>
    When <math|R> is an integral domain we have <math|U(R[X])=U(R)>. To see
    this, suppose that <math|p\<in\>U(R[X])>. Then there is some
    <math|q\<in\>U(R[X])> such that <math|p*q=1>, and so <math|0=deg p+deg
    q>, whence <math|deg p=0> and <math|deg q=0>. Thus <math|p(X)=a<rsub|0>>
    and <math|q(X)=b<rsub|0>> for some <math|a<rsub|0>,b<rsub|0>\<in\>R<rsup|\<ast\>>>.
    Since <math|a<rsub|0>b<rsub|0>=1> and <math|R> is commutative we have
    <math|b<rsub|0>a<rsub|0>=a<rsub|0>b<rsub|0>=1>, so
    <math|p(X)=a<rsub|0>\<in\>U(R)> as required. Conversely, if
    <math|p\<in\>U(R)> then <math|p\<in\>U(R[X])> and we are done.
  </example>

  <section|Ideals and quotients>

  Subrings are an important substructure of rings, but just as groups have
  subgroups and normal subgroups, rings have subrings and a further type of
  structure called an ideal. Normal subgroups are connected to quotient
  groups, and ideals are connected to quotient rings in the same way.

  Given an ring <math|R>, a <strong|left (resp. right) ideal> in <math|R> is
  a subgroup <math|I> of the additive group of <math|R> that is closed under
  multiplication on the left (resp. right) by all elements of <math|R>
  <em|i.e.> <math|I> is a subgroup with <math|r*x\<in\>I> (resp.
  <math|x*r\<in\>I>) for all <math|r\<in\>R> and <math|x\<in\>I>. An
  <strong|ideal> in <math|R> \U also called a <strong|two-sided ideal> \U is
  a left ideal and right ideal.

  <\remark>
    Left and right ideals are connected with the module structure of rings
    which we will examine more closely in the second part of the course. For
    now, two-sided ideals are our focus.
  </remark>

  <\observation>
    If <math|R> is commutative then every left ideal (resp. right) ideal is a
    (two-sided) ideal and hence a right (resp. left) ideal.
  </observation>

  <\example>
    In any ring <math|R> the sets <math|<around*|{|0|}>> and <math|R> are
    ideals called the <strong|zero ideal> and <strong|unit ideal>
    respectively.
  </example>

  <\observation>
    If <math|I> is a left (resp. right) ideal containing a unit <math|x> then
    for all <math|r\<in\>R>, <math|r*x<rsup|-1>*x\<in\>I> (resp.
    <math|x*x<rsup|-1>r\<in\>I>) so <math|I=R>. In particular, any left,
    right, or two-sided ideal containing a unit is the unit ideal.
  </observation>

  <\example>
    Every non-zero element of a field is a unit, and so any non-zero ideal is
    the unit ideal. In other words, fields have only two ideals.
  </example>

  <\example>
    Since every non-zero element of the quaternions <math|\<bbb-H\>> is a
    unit, the only ideals in <math|\<bbb-H\>> are the zero ideal and the unit
    ideal.
  </example>

  For <math|x\<in\>R> the set <math|R*x> is a left ideal, and <math|x*R> is a
  right ideal but neither, in general, is an ideal. The set

  <\equation*>
    <around*|\<langle\>|x|\<rangle\>>\<assign\><around*|{|r<rsub|1>*x*r<rsub|1><rprime|'>+\<cdots\>+r<rsub|n>*x*r<rsub|n><rprime|'>\<suchthat\>n\<in\>\<bbb-N\><rsub|0>,r<rsub|1>,\<ldots\>,r<rsub|n>,r<rsub|1><rprime|'>,\<ldots\>,r<rsub|n><rprime|'>\<in\>R|}>
  </equation*>

  is a subgroup by the subgroup test and is closed under multiplication on
  the left and right by elements of <math|R> and so is an ideal.
  <with|font|Segoe UI Emoji|\<#26A0\>>In general
  <math|<around*|\<langle\>|x|\<rangle\>>\<neq\>R*x*R>.

  <\example>
    In the ring <math|M<rsub|2><around*|(|\<bbb-F\>|)>> put

    <\equation*>
      A\<assign\><matrix|<tformat|<table|<row|<cell|1>|<cell|0>>|<row|<cell|0>|<cell|0>>>>><text|
      and >P\<assign\><matrix|<tformat|<table|<row|<cell|0>|<cell|1>>|<row|<cell|1>|<cell|0>>>>><text|
      so that >A+P*A*P=<matrix|<tformat|<table|<row|<cell|1>|<cell|0>>|<row|<cell|0>|<cell|1>>>>>
    </equation*>

    Then <math|1<rsub|2>=A+P*A*P\<in\><around*|\<langle\>|A|\<rangle\>>>, but
    <math|A> is not invertible so none of the matrices in
    <math|M<rsub|2><around*|(|\<bbb-F\>|)>> is invertible, and hence
    <math|M<rsub|2><around*|(|\<bbb-F\>|)>*A*M<rsub|2><around*|(|\<bbb-F\>|)>>
    is not a subgroup and <math|<around*|\<langle\>|A|\<rangle\>>\<neq\>M<rsub|2><around*|(|\<bbb-F\>|)>*A*M<rsub|2><around*|(|\<bbb-F\>|)>>.
  </example>

  If there is <math|x\<in\>R> such that <math|I=<around*|\<langle\>|x|\<rangle\>>>
  then we say <math|I> is <strong|principal> and is <strong|generated by>
  <math|x>. They are lines in vector space.

  <\example>
    For <math|N\<in\>\<bbb-N\><rsup|\<ast\>>>, the ideal
    <math|<around*|\<langle\>|N|\<rangle\>>> in <math|\<bbb-Z\>> is the set
    of multiples of <math|N>. Moreover, if <math|I> is a non-zero ideal in
    <math|\<bbb-Z\>> then it has a minimal positive element <math|N>. If
    <math|z\<in\>I>, then by the division algorithm we can write
    <math|z=N*w+r> for some <math|q\<in\>\<bbb-Z\>> and
    <math|0\<leqslant\>r\<less\>N>. But <math|r=z-N*w\<in\>I> and hence
    <math|r=0> by minimality of <math|N>, and so
    <math|I=<around*|\<langle\>|N|\<rangle\>>>. In particular, <em|every>
    ideal in <math|\<bbb-Z\>> is principal.
  </example>

  <\observation>
    Given (left, right, resp. two-sided) ideals
    <math|I<rsub|1>,\<ldots\>,I<rsub|n>> in a ring <math|R>,
    <math|I<rsub|1>+\<cdots\>+I<rsub|n>> and
    <em|><math|<big|cap><rsub|j=1><rsup|n>I<rsub|j>> are both (left, right,
    resp. two-sided) ideals.

    For <math|x<rsub|1>,\<ldots\>,x<rsub|n>\<in\>R> we define
    <math|<around*|\<langle\>|x<rsub|1>,\<ldots\>,x<rsub|n>|\<rangle\>>\<assign\><around*|\<langle\>|x<rsub|1>|\<rangle\>>+\<cdots\>+<around*|\<langle\>|x<rsub|n>|\<rangle\>>>,
    and call it the <strong|ideal generated by>
    <math|x<rsub|1>,\<ldots\>,x<rsub|n>>. We say that an ideal is
    <strong|finitely generated> if <math|I=<around*|\<langle\>|x<rsub|1>,\<ldots\>,x<rsub|n>|\<rangle\>>>
    for some <math|x<rsub|1>,\<ldots\>,x<rsub|n>>.
  </observation>

  <\remark>
    Rings in which every ideal is finitely generated are called
    <strong|Noetherian> rings and these, and their close cousins for left and
    right ideals, are very important but will not be our focus in this
    course.
  </remark>

  <\example>
    The algebraic integers contain an ideal that is not finitely generated.
    Exercise II.4 develops a proof of this.
  </example>

  <\example>
    The ideal <math|<around*|\<langle\>|2,X|\<rangle\>>> in
    <math|\<bbb-Z\><around*|[|X|]>> is the set of polynomials with even
    constant coefficient. Certainly the polynomials with even constant
    coefficient form an ideal in <math|\<bbb-Z\>[X]> containing 2 and
    <math|X>, and conversely every such polynomial is in
    <math|<around*|\<langle\>|2,X|\<rangle\>>> since it can be written in the
    form <math|2q<around*|(|X|)>+X*p<around*|(|X|)>> for some
    <math|p\<in\>\<bbb-Z\><around*|[|X|]>> and constant polynomial
    <math|q\<in\>\<bbb-Z\><around*|[|X|]>>.

    The ideal <math|<around*|\<langle\>|2,X|\<rangle\>>> is not principal. To
    see this, suppose that <math|p\<in\><around*|\<langle\>|2,X|\<rangle\>>>
    were such that <math|<around*|\<langle\>|2,X|\<rangle\>>=<around*|\<langle\>|p|\<rangle\>>>.
    Since <math|2\<in\><around*|\<langle\>|p|\<rangle\>>=p<around*|(|X|)>*\<bbb-Z\><around*|[|X|]>>
    there is <math|r\<in\>\<bbb-Z\><around*|[|X|]>> such that <math|2=p*r>.
    But <math|0=deg 2=deg p+deg r>, so <math|deg p=0>; say
    <math|p<around*|(|X|)>=a> for <math|a\<in\>\<bbb-Z\><rsup|\<ast\>>>.
    Since <math|X\<in\><around*|\<langle\>|p|\<rangle\>>=p<around*|(|X|)>\<bbb-Z\><around*|[|X|]>>
    there is <math|q\<in\>\<bbb-Z\><around*|[|X|]>> such that
    <math|X=p<around*|(|X|)>q<around*|(|X|)>>, and hence
    <math|1=p<around*|(|1|)>q<around*|(|1|)>=a*q<around*|(|1|)>>. Hence
    <math|p<around*|(|X|)>=\<pm\>1> and <math|<around*|\<langle\>|p|\<rangle\>>=\<bbb-Z\><around*|[|X|]>>
    contradicting the fact that <math|<around*|\<langle\>|2,X|\<rangle\>>\<neq\>\<bbb-Z\><around*|[|X|]>>.
  </example>

  <subsection|Quotient rings>

  Ideals are particularly important because they let us generalise the
  construction of the rings <math|\<bbb-Z\><rsub|N>> from <math|\<bbb-Z\>>.

  <\theorem>
    Suppose that <math|R> is a ring and <math|I> is an ideal. Then the
    commutative group <math|R/I> may be endowed with a multiplication such
    that the quotient map <math|q:R\<rightarrow\>R/I;x\<mapsto\>x+I> is a
    surjective ring homomorphism with kernel<\footnote>
      A ring homomorphism is, in particular, a group homomorphism and so has
      a kernel.
    </footnote> <math|I>. If <math|R> is commutative then so is this
    multiplication.
  </theorem>

  <\proof>
    <math|I> is a subgroup of a commutative group and so normal, and so by
    the quotient group construction <math|R/I> is a commutative group and
    <math|q> is a surjective group homomorphism with kernel <math|I>. We may
    define <wide|\<times\>|^> on <math|R/I>: first, for <math|u,v\<in\>R/I>
    let <math|x,y\<in\>R> be such that <math|q(x)=u> and <math|q(y)=v>. Then
    put <math|u<wide|\<times\>|^>v\<assign\>q(x*y)>; to show this is
    well-defined, we show that <math|q(x*y)=q(x<rprime|'>y<rprime|'>)>
    whenever <math|x+I=x<rprime|'>+I> and <math|y+I=y<rprime|'>+I>. By
    distributivity of multiplication and negation we have that
    <math|x*y\<minus\>x<rprime|'>y<rprime|'>=(x\<minus\>x<rprime|'>)y+x<rprime|'>(y\<minus\>y<rprime|'>)>.
    But then <math|x\<minus\>x<rprime|'>\<in\>I> and
    <math|y\<minus\>y<rprime|'>\<in\>I> and so
    <math|x*y\<minus\>x<rprime|'>y<rprime|'>\<in\>I*y+x<rprime|'>I\<subset\>I>
    since <math|I> is closed under multiplication by <em|any> element of
    <math|R> (in this case <math|y> on the right and <math|x<rprime|'>> on
    the left). We conclude that <math|q(x*y)=q(x<rprime|'>y<rprime|'>)> as
    required.

    For <math|u,v,w\<in\>R/I>, let <math|x,y,z\<in\>R> be such that
    <math|u=q(x),v=q(y)> and <math|w=q(z)>. Then
    <math|(u<wide|\<times\>|^>v)<wide|\<times\>|^>w=q((x*y)z)=q(x(y*z))=u<wide|\<times\>|^>(v<wide|\<times\>|^>w)>
    so that <wide|\<times\>|^> is associative. <math|q(1)q(x)=q(x)=q(x)q(1)>
    so <math|q(1)> is an identity for <wide|\<times\>|^> since <math|q> is
    surjective. Finally, for <math|q(x)\<in\>R/I>, we have
    <math|q(x)<wide|\<times\>|^>(q(y)+q(z))=q(x(y+z))=q(x*y+x*z)=q(x*y)+q(x*z)=q(x)<wide|\<times\>|^>q(y)+q(x)<wide|\<times\>|^>q(z)>
    and since <math|q> is surjective it follows that left multiplication by
    <math|q(x)> is a homomorphism. So is right multiplication by a similar
    argument, and hence (again since <math|q> is surjective) it follows that
    <wide|\<times\>|^> distributes over addition.

    Finally, we have seen that <math|q(1)> is the identity; <math|q> is a
    homomorphism of the additive group by definition of the quotient group;
    and <math|q> is multiplicative by definition. Thus <math|q> is a ring
    homomorphism. Moreover, <wide|\<times\>|^> is visibly commutative if the
    multiplication on <math|R> is commutative. The result is proved.
  </proof>

  Since the map <math|q> above is a surjective ring homomorphism the
  multiplication on <math|R/I> is determined by <math|q>:
  <math|1<rsub|R/I>=1+I;(x+I)\<times\><rsub|R/I>(y+I)=(x*y)+I> for all
  <math|x,y\<in\>R>; and if <math|x\<in\>U(R)> then <math|x+I\<in\>U(R/I)>
  and <math|(x+I)<rsup|\<minus\>1>=x<rsup|\<minus\>1>+I>, where the first
  <math|(\<cdot\>)<rsup|\<minus\>1>> is multiplicative inversion in
  <math|R/I>, and the second is in <math|R>.

  By <em|the> ring <math|R/I> we mean this ring structure and we call this
  the <strong|quotient ring (of <math|R> by <math|I>)>.

  <\example>
    The ring of integers <math|\<bbb-Z\>> has <math|\<langle\>N\<rangle\>> as
    an ideal, and the quotient ring <math|\<bbb-Z\>/\<langle\>N\<rangle\>> is
    none other than the ring <math|\<bbb-Z\><rsub|N>>.
  </example>

  Formally <math|\<bbb-Z\><rsub|N>> is realised as a set of cosets, but this
  can lead to burdensome notation so in practice we just do arithmetic with
  the integers as usual, but with a coarser notion of equality: that of
  equivalence <math|<pmod|N>>. The fact that we can do this is exactly the
  fact that the quotient map <math|q> is a ring homomorphism.

  The same notational convenience is useful in polynomial rings. If
  <math|f\<in\>\<bbb-F\>[X]<rsup|\<ast\>>> we write <math|p\<equiv\>q (mod
  f)> to mean that <math|p+\<langle\>f\<rangle\>=q+\<langle\>f\<rangle\>> or,
  equivalently, that <math|p\<minus\>q> is a multiple of <math|f>. We can do
  arithmetic in <math|\<bbb-F\>[X]/\<langle\>f\<rangle\>> by doing it first
  in <math|\<bbb-F\>[X]> and then declaring two results to be equivalent if
  they differ by a multiple of <math|f>.

  <\proposition>
    Suppose that <math|f\<in\>\<bbb-F\>[X]<rsup|\<ast\>>> has degree
    <math|d>. The map <math|\<bbb-F\>\<times\>\<bbb-F\>[X]/\<langle\>f\<rangle\>\<rightarrow\>\<bbb-F\>[X]/\<langle\>f\<rangle\>;(\<lambda\>,p
    (mod f))\<mapsto\>\<lambda\>p (mod f)><math|> is a scalar multiplication
    of <math|\<bbb-F\>> on the additive group of
    <math|\<bbb-F\>[X]/\<langle\>f\<rangle\>> such that the ring
    multiplication maps are linear and <math|1,X,\<ldots\>,X<rsup|d\<minus\>1>>
    is a basis.
  </proposition>

  <\proof>
    For the first part it is enough to note that the inclusion map
    <math|\<bbb-F\>\<rightarrow\>\<bbb-F\>[X]> composed with the quotient map
    <math|\<bbb-F\>[X]\<rightarrow\>\<bbb-F\>[X]/\<langle\>f\<rangle\>>
    induces an <math|\<bbb-F\>>-vector space structure with the given scalar
    multiplication such that the ring multiplication maps are linear.

    To see that <math|1,X,\<ldots\>,X<rsup|d>> is spanning, note that by the
    division algorithm for polynomials, for every <math|g\<in\>\<bbb-F\>[X]>
    there is <math|q,r\<in\>\<bbb-F\>[X]> with <math|g(X)=f(X)q(X)+r(X)> and
    <math|r(X)=a<rsub|0>+\<cdots\>+a<rsub|d\<minus\>1>X<rsup|d\<minus\>1>>,
    whence <math|g(X)\<equiv\>a<rsub|0>+\<cdots\>+a<rsub|d\<minus\>1>X<rsup|d\<minus\>1>
    (mod f)>.

    To see that <math|1,X,\<ldots\>,X<rsup|d>> is linearly independent,
    suppose that <math|a<rsub|0>,\<ldots\>,a<rsub|d\<minus\>1>\<in\>\<bbb-F\>>
    have <math|a<rsub|0>+a<rsub|1>X+\<cdots\>+a<rsub|d\<minus\>1>X<rsup|d\<minus\>1>\<equiv\>0
    (mod f)>. If the <math|a<rsub|i>>s are not all 0 then the polynomial
    <math|r(X)=a<rsub|0>+a<rsub|1>X+\<cdots\>+a<rsub|d\<minus\>1>X<rsup|d\<minus\>1>>
    has a degree, and its degree is at most <math|d\<minus\>1>. This
    contradicts the fact it is divisible by <math|f>.
  </proof>

  <\example>
    The ring <math|R[X]/\<langle\>X<rsup|2>\<rangle\>> is called the ring of
    <strong|dual numbers>, and in this ring we have
    <math|(1+X)<rsup|n>\<equiv\>1+n*X (mod X<rsup|2>)>. So for a polynomial
    <math|f> we have <math|f(1+X)\<equiv\>f(1)+f<rprime|'>(1)X (mod
    X<rsup|2>)> where <math|f<rprime|'>> denotes the usual derivative of
    <math|f>.
  </example>

  <\example>
    In the ring <math|R[X]/\<langle\>X<rsup|2>+1\<rangle\>>, we have

    <\equation*>
      (a+b*X)+(c+d*X)\<equiv\>(a+c)+(b+d)X (mod X<rsup|2>+1)
    </equation*>

    and

    <\equation*>
      (a+b*X)(c+d*X)\<equiv\>(a*c\<minus\>b*d)+(b*c+a*d)X (mod X<rsup|2>+1).
    </equation*>

    These are the same rules for arithmetic as those on the complex numbers
    with <math|X> replaced by <math|i>. Put formally, the map

    <\equation*>
      \<phi\>:\<bbb-C\>\<rightarrow\>\<bbb-R\>[X]/\<langle\>X<rsup|2>+1\<rangle\>;a+b*i\<mapsto\>a+b*X
      (mod X<rsup|2>+1)
    </equation*>

    is a ring homomorphism. Moreover, <math|\<phi\>> is a surjection because
    <math|{1,X}> is a basis for the codomain, so every
    <math|f\<in\>\<bbb-R\>[X]/\<langle\>X<rsup|2>+1\<rangle\>> can be written
    as <math|f\<equiv\>a+b*X (mod X<rsup|2>+1)> for some
    <math|a,b\<in\>\<bbb-R\>>, and hence <math|f\<equiv\>\<phi\>(a+b*i) (mod
    X<rsup|2>+1)>; and <math|\<phi\>> is an injection because it is a group
    homomorphism, and if <math|\<phi\>(a+b*i)\<equiv\>0 (mod X<rsup|2>+1)>
    then <math|a+b*i=0> since <math|{1,X}> is a basis. Thus <math|\<bbb-C\>>
    and <math|\<bbb-R\>[X]/\<langle\>X<rsup|2>+1>\<rangle\> are isomorphic.
  </example>

  <subsection|The Chinese Remainder Theorem>

  If <math|I,J> are ideals, then <math|I+J> is an ideal. We say <math|I> is
  finitely generated if <math|I=<around*|\<langle\>|x<rsub|1>|\<rangle\>>+\<cdots\>+<around*|\<langle\>|x<rsub|n>|\<rangle\>>>.

  <\theorem>
    Suppose that <math|R> is a ring and <math|I<rsub|1>,\<ldots\>,I<rsub|n>>
    are ideals with <math|I<rsub|i>+I<rsub|j>=R> for all <math|i\<neq\>j>.
    Then the map

    <\equation*>
      \<psi\>:R\<rightarrow\>(R/I<rsub|1>)\<times\>\<cdots\>\<times\>(R/I<rsub|n>);x\<mapsto\>(x+I<rsub|1>,\<ldots\>,x+I<rsub|n>)
    </equation*>

    is a surjective ring homomorphism.
  </theorem>

  <\proof>
    The given map is certainly a ring homomorphism; the content of this proof
    is surjectivity: For <math|j\<neq\>i> since
    <math|1\<in\>R=I<rsub|i>+I<rsub|j>>, we can find
    <math|y<rsub|i,j>\<in\>I<rsub|j>,1-y*<rsub|i,j>\<in\>I<rsub|i>>, and put
    <math|w<rsub|i>\<assign\>y<rsub|i,1>\<cdots\>y<rsub|i,i\<minus\>1>\<cdot\>y<rsub|i,i+1>\<cdots\>y<rsub|i,n>>.
    Then <math|w<rsub|i>+I<rsub|j>=I<rsub|j>> for all <math|j\<neq\>i>; and
    <math|w<rsub|i>+I<rsub|i>=1+I<rsub|i>>. In particular for all
    <math|1\<leqslant\>i\<leqslant\>n> we have
    <math|\<psi\>(w<rsub|i>)=(0<rsub|R/I<rsub|1>>,\<ldots\>,0<rsub|R/I<rsub|i\<minus\>1>>,1<rsub|R/I<rsub|i>>,0<rsub|R/I<rsub|i+1>>,\<ldots\>,0<rsub|R/I<rsub|n>>)>
    and so if <math|z\<in\>R<rsup|n>> then
    <math|\<psi\>(z<rsub|1>w<rsub|1>+\<cdots\>+z<rsub|n>w<rsub|n>)
    =(z<rsub|1>+I<rsub|1>,\<ldots\>,z<rsub|n>+I<rsub|n>)> and the map is
    surjective as claimed.
  </proof>

  <\remark>
    For <math|G> a group and <math|H<rsub|1>,H<rsub|2>\<leqslant\>G> with
    <math|H<rsub|1>H<rsub|2>=G> the map <math|G\<rightarrow\>(G/H<rsub|1>)\<times\>(G/H<rsub|2>);x\<mapsto\>(x*H<rsub|1>,x*H<rsub|2>)>
    is surjective though the codomain need not even be a group; the substance
    of Theorem 2.18 is in the fact it applies for <math|n\<gtr\>2>.
  </remark>

  <\remark>
    The history of this theorem is involved \U see [She88] \U but the
    starting point is work of Sun Zi (\<#5B6B\>\<#5B50\>) from around 400AD
    with the particular problem of finding an integer <math|z> such that
    <math|z\<equiv\>2 (mod 3),z\<equiv\>3 (mod 5),> and <math|z\<equiv\>2
    (mod 7)>. To connect this to Theorem 2.18 note that 3, 5, and 7 are
    coprime in pairs, so Bezout's Lemma tells us that\ 

    <\equation*>
      \<langle\>3\<rangle\>+\<langle\>5\<rangle\>=\<bbb-Z\>,\<langle\>3\<rangle\>+\<langle\>7\<rangle\>=\<bbb-Z\>,<text|<math|
      and >>\<langle\>5\<rangle\>+\<langle\>7\<rangle\>=\<bbb-Z\>,
    </equation*>

    and hence the map

    <\equation*>
      \<bbb-Z\>\<rightarrow\>\<bbb-Z\><rsub|3>\<times\>\<bbb-Z\><rsub|5>\<times\>\<bbb-Z\><rsub|7>;z\<mapsto\>(z
      (mod 3),z (mod 5),z (mod 7))
    </equation*>

    is surjective from which we can conclude that an integer satisfying the
    desired congruences exists.
  </remark>

  <subsection|The First Isomorphism Theorem and consequences>

  <\theorem>
    <dueto|First Isomorphism Theorem>Suppose that
    <math|\<phi\>:R\<rightarrow\>S> is a ring homomorphism. Then <math|ker
    \<phi\>> is an ideal in <math|R>, and the map

    <\equation*>
      <wide|\<phi\>|~>:R/ker \<phi\>\<rightarrow\>S;x+ker
      \<phi\>\<mapsto\>\<phi\>(x)
    </equation*>

    is a well-defined injective ring homomorphism. In particular, <math|R/ker
    \<phi\>> is isomorphic to <math|Im \<phi\>>.
  </theorem>

  <\proof>
    Since <math|\<phi\>> is a group homomorphism the kernel is an additive
    subgroup of <math|R>. Now suppose <math|x\<in\>ker \<phi\>> and
    <math|r\<in\>R>. Then <math|\<phi\>(x*r)=\<phi\>(x)\<phi\>(r)=0\<phi\>(r)=0>
    since zero annihilates, and similarly <math|\<phi\>(r*x)=0>. It follows
    that <math|x*r,r*x\<in\>ker \<phi\>> so that <math|ker \<phi\>> is an
    ideal.

    The map <math|<wide|\<phi\>|~>> is a well-defined injective group
    homomorphism by the First Isomorphism Theorem for groups. In addition,

    <\align>
      <tformat|<table|<row|<cell|<wide|\<phi\>|~>((x+ker \<phi\>)(y+ker
      \<phi\>))>|<cell|=<wide|\<phi\>|~>((x*y)+ker
      \<phi\>)>>|<row|<cell|>|<cell|=\<phi\>(x*y)=\<phi\>(x)\<phi\>(y)=<wide|\<phi\>|~>(x+ker
      \<phi\>)<wide|\<phi\>|~>(y+ker \<phi\>),>>>>
    </align>

    and <math|<wide|\<phi\>|~>(1<rsub|R>+ker
    \<phi\>)=\<phi\>(1<rsub|R>)=1<rsub|S>>. The result is proved.
  </proof>

  <\example>
    For <math|R> a subring of <math|S> and <math|\<lambda\>\<in\>S> commuting
    with all elements of <math|R>, the kernel of the evaluation homomorphism
    at <math|\<lambda\>> extending the inclusion homomorphism
    <math|R\<rightarrow\>S>, that is the set
    <math|{p\<in\>R[X]:p(\<lambda\>)=0}> of polynomials of which
    <math|\<lambda\>> is a root, is an ideal.
  </example>

  The First Isomorphism Theorem is often used to show that a given ring
  homomorphism is well-defined by showing that it arises by factoring a
  homomorphism that is more easily seen to be well-defined.

  <\example>
    The map <math|\<psi\>> from the Chinese Remainder Theorem (Theorem 2.18)
    is a surjective ring homomorphism with <math|ker
    \<psi\>={x\<in\>R:x\<in\>I<rsub|i><text| for all
    >i}=I<rsub|1>\<cap\>\<cdots\>\<cap\>I<rsub|n>>, and hence by the First
    Isomorphism Theorem we have an isomorphism between
    <math|R/(I<rsub|1>\<cap\>\<cdots\>\<cap\>I<rsub|n>)> and
    <math|(R/I<rsub|1>)\<times\>\<cdots\>\<times\>(R/I<rsub|n>)> when
    <math|I<rsub|1>,\<ldots\>,I<rsub|n>> are ideals in <math|R> with
    <math|I<rsub|i>+I<rsub|j>=R> for all <math|i\<neq\>j>.
  </example>

  <\example>
    Given a ring homomorphism <math|\<phi\>:R\<rightarrow\>S> and an ideal
    <math|J> contained in <math|ker \<phi\>>, the map
    <math|R/J\<rightarrow\>S;x+J\<mapsto\>\<phi\>(x)> is a well-defined ring
    homomorphism: Apply the First Isomorphism Theorem to the map
    <math|R\<rightarrow\>(R/J)\<times\>S;x\<mapsto\>(x+J,\<phi\>(x))>. The
    kernel of this map is <math|J> since <math|J\<subset\>ker \<phi\>> and
    hence the map <math|R/J\<rightarrow\>(R/J)\<times\>S;x+J\<mapsto\>(x+J,\<phi\>(x))>
    is a well-defined ring homomorphism and the result follows by composition
    with projection onto the second factor.
  </example>

  <subsection|Relationship between ideals in <math|R> and <math|R/I>>

  Given an ideal <math|I> in <math|R> we write <math|Ideals<rsub|I>(R)> for
  the set of ideals <math|J> in <math|R> with <math|I\<subset\>J>, and
  <math|Ideals(R)>(= <math|Ideals<rsub|{0}>(R)>) for the set of ideals of
  <math|R>.

  <\theorem>
    Suppose that <math|R> is a ring and <math|I> is an ideal in <math|R>.
    Write <math|q:R\<rightarrow\>R/I> for the quotient map
    <math|x\<mapsto\>x+I>. Then the map

    <\equation*>
      \<phi\>:Ideals<rsub|I> (R)\<rightarrow\>Ideals(R/I);I<rprime|'>\<mapsto\>q(I<rprime|'>)
    </equation*>

    is a well-defined inclusion-preserving bijection.
  </theorem>

  <\proof>
    Since <math|q> is a surjective ring homomorphism, if <math|I<rprime|'>>
    is an ideal in <math|R> then <math|q(I<rprime|'>)> is an ideal and the
    map is well-defined. It is visibly inclusion-preserving. If <math|J> is
    an ideal in <math|R/I> then <math|q<rsup|\<minus\>1>(J)> is an ideal in
    <math|R> since <math|q> is a ring homomorphism. Since
    <math|I=0<rsub|R/I>\<in\>J> we have <math|I\<subset\>q<rsup|\<minus\>1>(J)>,
    and hence <math|q<rsup|\<minus\>1>(J)\<in\>Ideals<rsub|I>(R)>. Since
    <math|q> is surjective <math|q(q<rsup|\<minus\>1>(J))=J>, and so
    <math|\<phi\>> is surjective. Finally, if
    <math|I<rprime|'>\<neq\>I<rprime|''>> are two ideals containing <math|I>
    then <math|I<rprime|'>+I=I<rprime|'>\<neq\>I<rprime|''>=I<rprime|''>+I>
    and so, without loss of generality, there is <math|x\<in\>I<rprime|''>>
    such that <math|(x+I)\<cap\>I<rprime|'>=\<varnothing\>>. It follows that
    <math|q(x)\<notin\>q(I<rprime|'>)>, and hence
    <math|q(I<rprime|'>)\<neq\>q(I<rprime|''>)>. In particular,
    <math|\<phi\>> is injective.
  </proof>

  This result also goes by the name of the Correspondence Theorem and
  sometimes the Fourth Isomorphism Theorem for rings.

  <\example>
    <dueto|Example 1.13, contd.><math|\<bbb-Z\><rsub|N>> is a ring in which
    every ideal is principal. To see this, let
    <math|\<phi\>:Ideals<rsub|\<langle\>N\<rangle\>>(\<bbb-Z\>)\<rightarrow\>Ideals(\<bbb-Z\><rsub|N>)>
    be the map from the Correspondence Theorem and suppose <math|J> is an
    ideal in <math|\<bbb-Z\><rsub|N>>. Since every ideal in <math|\<bbb-Z\>>
    is principal, <math|\<phi\><rsup|\<minus\>1>(J)=\<langle\>M\<rangle\>>
    for some <math|M\<in\><math|\<bbb-N\><rsup|\<ast\>>>>, and furthermore
    <math|\<langle\>M\<rangle\>\<supset\>\<langle\>N\<rangle\>>. Since
    <math|\<phi\>> is a bijection, <math|J=\<phi\>(\<langle\>M\<rangle\>)={M*z
    (mod N):z\<in\>\<bbb-Z\>}=\<langle\>M (mod N)\<rangle\>> is principal.

    <math|<around*|\<langle\>|15|\<rangle\>>\<subset\><around*|\<langle\>|3|\<rangle\>>,<around*|\<langle\>|5|\<rangle\>>\<subset\>\<bbb-Z\>=<around*|\<langle\>|1|\<rangle\>>>
    corresponds to the ideal structure of
    <math|\<bbb-Z\>/<around*|\<langle\>|15|\<rangle\>>>:

    <math|<around*|\<langle\>|3|\<rangle\>><rsub|\<bbb-Z\>/<around*|\<langle\>|15|\<rangle\>>>=<around*|{|0
    mod 15,3 mod 15,\<ldots\>,12 mod 15|}>>

    <math|<around*|\<langle\>|5|\<rangle\>><rsub|\<bbb-Z\>/<around*|\<langle\>|15|\<rangle\>>>=<around*|{|0
    mod 15,5 mod 15,10 mod 15|}>>
  </example>

  <subsection|Proper, prime, and maximal ideals>

  Some of the properties of ideals are reflected in properties of quotient
  rings, and we will look at three important ones now. An ideal <math|I> is
  <strong|proper> if <math|1\<notin\>I> or, equivalently, <math|I\<neq\>R>.

  <\observation>
    An ideal <math|I> is proper if and only if <math|R/I> is non-trivial
    since <math|1<rsub|R/I>\<neq\>0<rsub|R/I>> if and only if
    <math|1+I\<neq\>I>, if and only if <math|1\<notin\>I>.
  </observation>

  We say that an ideal <math|I> is <strong|prime> if it is proper and
  whenever <math|a*b\<in\>I> we have either <math|a\<in\>I> or
  <math|b\<in\>I>.

  <\proposition>
    Suppose that <math|R> is a commutative ring and <math|I> is an ideal in
    <math|R>. Then <math|I> is prime if and only if <math|R/I> is an integral
    domain. In particular <math|R> is an integral domain if and only if
    <math|{0<rsub|R>}> is prime.
  </proposition>

  <\proof>
    \ For `only if' we have <math|(a+I)(b+I)=0<rsub|R/I>=I>, so
    <math|a*b\<in\>I> and therefore <math|a\<in\>I> or <math|b\<in\>I> by
    primality. Consequently <math|a+I=I=0<rsub|R/I>> or
    <math|b+I=I=0<rsub|R/I>> <em|i.e.> <math|R/I> is an integral domain.
    (<math|R/I> is non-trivial since <math|I> is proper.) In the other
    direction, <math|I> is proper since <math|R/I> is non-trivial, and if
    <math|a*b\<in\>I> then <math|(a+I)(b+I)=0<rsub|R/I>>, and
    <math|a+I=0<rsub|R/I>=I> or <math|b+I=0<rsub|R/I>=I>. We conclude
    <math|a\<in\>I> or <math|b\<in\>I> as required.
  </proof>

  We say that an ideal <math|I> is <strong|maximal> if <math|I> is proper and
  whenever <math|I\<subset\>J\<subset\>R> for some ideal <math|J> we have
  <math|J=I> or <math|J=R>.

  <with|font|Segoe UI Emoji|\<#26A0\>>Maximal here is maximal with respect to
  inclusion amongst <em|proper> ideals; all ideals in <math|R> are contained
  in the ideal <math|R>.

  <\proposition>
    Suppose that <math|R> is a commutative ring and <math|I> is an ideal in
    <math|R>. Then <math|I> is maximal if and only if <math|R/I> is a field.
  </proposition>

  <\proof>
    Suppose that <math|R/I> is a field. Then <math|R/I> is non-trivial and so
    <math|I> is proper; suppose <math|J> is an ideal with
    <math|I\<subsetneq\>J\<subset\>R>. There is <math|x\<in\>J\<setminus\>I>
    and since <math|R/I> is a field there is some <math|y\<in\>R> such that
    <math|x*y+I=1+I> whence <math|1\<in\>x*R+I\<subset\>J> and so <math|J=R>,
    whence <math|I> is maximal as claimed.

    Conversely, if <math|I> is maximal and <math|x\<in\>R> has
    <math|x+I\<neq\>I> then <math|I+x*R> is an ideal properly containing
    <math|I> and so by maximality equals <math|R>. It follows that there is
    some <math|y\<in\>R> such that <math|1\<in\>x*y+I> whence
    <math|(x+I)(y+I)=1<rsub|R/I>> so that <math|U(R/I)=(R/I)<rsup|\<ast\>>>
    and <math|R/I> is a field as required.(<math|R/I> is non-trivial as
    <math|I> is proper.)
  </proof>

  <subsection|Discussion of fields of fractions and their characterisation>

  A subring of an integral domain is an integral domain and so, in
  particular, a subring of a field is an integral domain. Conversely we have
  the following:

  <\theorem>
    Suppose that <math|R> is an integral domain. Then there is a field
    <math|\<bbb-F\>> containing <math|R> as a subring.
  </theorem>

  <\remark>
    The proof of this is omitted, but such a field can be constructed in a
    similar way to the way to which one constructs the integers from the
    naturals by `adding in' the negative numbers.
  </remark>

  For <math|R> an integral domain and <math|\<bbb-F\>> a field containing
  <math|R> the <strong|field of fractions of <math|R> in <math|\<bbb-F\>>> is
  the field <math|Frac<rsub|\<bbb-F\>>(R):={a*b<rsup|\<minus\>1>:a\<in\>R,b\<in\>R<rsup|\<ast\>>}>.
  This is a subring of <math|\<bbb-F\>> containing <math|R> by the subring
  test since it contains <math|1=1.1<rsup|\<minus\>1>>, and is closed under
  subtraction and multiplication since

  <\equation*>
    a*c<rsup|\<minus\>1>\<minus\>b*d<rsup|\<minus\>1>=(a*d\<minus\>b*c)(c*d)<rsup|\<minus\>1><text|
    and >(a*c<rsup|\<minus\>1>)(b*d<rsup|\<minus\>1>)=(a*b)(c*d)<rsup|\<minus\>1>
  </equation*>

  Now, if <math|a*b<rsup|\<minus\>1>\<neq\>0> then
  <math|a\<in\>R<rsup|\<ast\>>> so <math|b*a<rsup|-1>\<in\>Frac<rsub|\<bbb-F\>><around*|(|R|)>>,
  and hence <math|Frac<rsub|\<bbb-F\>>(R)> is closed under multiplicative
  inverses and so a field.

  For the most part the containing field <math|\<bbb-F\>> will be clear \U
  indeed it will very often be <math|\<bbb-C\>> \U in which case we write
  <math|Frac(R)> for <math|Frac<rsub|\<bbb-F\>>(R)>.

  <\example>
    The field of fractions of <math|\<bbb-Z\>> in <math|\<bbb-C\>> is
    <math|\<bbb-Q\>>, and this is the prototype.
  </example>

  <\observation>
    If <math|R\<subset\>\<bbb-K\>\<subset\>\<bbb-F\>> for fields
    <math|\<bbb-K\>> and <math|\<bbb-F\>>, then
    <math|Frac<rsub|\<bbb-F\>><around*|(|\<bbb-R\>|)>\<subset\>\<bbb-K\>>. In
    particular, <math|Frac<rsub|\<bbb-F\>><around*|(|\<bbb-K\>|)>=\<bbb-K\>>.
  </observation>

  Our definition of field of fractions characterises it in the following
  sense:

  <\theorem>
    Suppose that <math|\<bbb-F\>> and <math|\<bbb-K\>> are fields containing
    <math|R> as a subring. Then there is a unique isomorphism
    <math|\<phi\>:Frac<rsub|\<bbb-F\>>(R)\<rightarrow\>Frac<rsub|\<bbb-K\>>(R)>
    such that <math|\<phi\>(r)=r> for all <math|r\<in\>R>.
  </theorem>

  <\remark>
    Again we omit the proof, but the idea is to define <math|\<phi\>> by
    <math|\<phi\>(r*s<rsup|\<minus\>1>)\<assign\>r*s<rsup|\<minus\>1>> for
    <math|r\<in\>R> and <math|s\<in\>R<rsup|\<ast\>>>. <with|font|Segoe UI
    Emoji|\<#26A0\>><math|s<rsup|\<minus\>1>> on the left is the inverse of
    <math|s> in <math|\<bbb-F\>>, and on the right in <math|\<bbb-K\>>.
  </remark>

  <\example>
    We write <math|\<bbb-Q\>(i)> for their field of fractions of the Gaussian
    integers inside <math|\<bbb-C\>>. Since
    <math|\<bbb-Z\>\<subset\>\<bbb-Z\><around*|[|i|]>> we must have
    <math|\<bbb-Q\>\<subset\>\<bbb-Q\>(i)>, and since
    <math|i\<in\>\<bbb-Z\><around*|[|i|]>> we must have
    <math|\<bbb-Q\>+i\<bbb-Q\>\<subset\>\<bbb-Q\>(i)>. On the other hand by
    the subring test <math|\<bbb-Q\>+i\<bbb-Q\>> is a subring of
    <math|\<bbb-C\>>, and if <math|0\<neq\>a+b*i\<in\>\<bbb-Q\>[i]> then

    <\equation*>
      <around|(|a+b*i|)><rsup|-1>=<frac|a|a<rsup|2>+b<rsup|2>>+i<frac|-b|a<rsup|2>+b<rsup|2>>\<in\>\<bbb-Q\>+i*\<bbb-Q\>
    </equation*>

    so <math|\<bbb-Q\>+i\<bbb-Q\>> is a field and hence
    <math|\<bbb-Q\><around*|(|i|)>=\<bbb-Q\>+i\<bbb-Q\>>.
  </example>

  <with|font|Segoe UI Emoji|\<#26A0\>>Complex conjugation
  <math|\<bbb-Q\><around*|(|i|)>\<rightarrow\>\<bbb-Q\><around*|(|i|)>;z\<mapsto\><wide|z|\<wide-bar\>>>
  is an isomorphism that is different from the identity map
  <math|\<bbb-Q\><around*|(|i|)>\<rightarrow\>\<bbb-Q\><around*|(|i|)>;z\<mapsto\>z>
  isomorphism, but complex conjugation is not the identity on
  <math|\<bbb-Z\><around*|[|i|]>>, and hence this does not violate the
  uniqueness of the isomorphism in Theorem 2.34.

  <subsection|Field extensions>

  We say that <math|\<bbb-K\>> is a <strong|field extension> of
  <math|\<bbb-F\>> if <math|\<bbb-K\>> is a field and <math|\<bbb-F\>> is a
  subfield of <math|\<bbb-K\>>. Given a field extension <math|\<bbb-K\>> of
  <math|\<bbb-F\>>, the inclusion map <math|\<bbb-F\>\<rightarrow\>\<bbb-K\>>
  induces an <math|\<bbb-F\>>-vector space structure on <math|\<bbb-K\>>
  (such that the multiplication maps on <math|\<bbb-K\>> are
  <math|\<bbb-F\>>-linear) and we call the dimension of this the
  <strong|degree> of the field extension, denoted
  <math|<around*|\||\<bbb-K\>:\<bbb-F\>|\|>>.

  Given a field extension <math|\<bbb-K\>> of <math|\<bbb-F\>>, we say
  <math|\<alpha\>\<in\>\<bbb-K\>> is <strong|<math|\<bbb-F\>>-algebraic> if
  there is some <math|p\<in\>\<bbb-F\>[X]<rsup|\<ast\>>> such that
  <math|p(\<alpha\>)=0>, and it is <strong|<math|\<bbb-F\>>-transcendental>
  if there is no such polynomial.

  <\example>
    <math|\<bbb-C\>> is a field extension of <math|\<bbb-R\>> of degree 2,
    and <em|any> <math|z\<in\>\<bbb-C\>> is <math|\<bbb-R\>>-algebraic since
    <math|p(X)\<assign\>X<rsup|2>\<minus\>2 Re z*X+<around*|\||z|\|><rsup|2>>
    has <math|p\<in\>R[X]<rsup|\<ast\>>> and <math|p(z)=0>.
  </example>

  <\example>
    <math|\<bbb-R\>> is an infinite degree field extension of
    <math|\<bbb-Q\>>, and <math|\<alpha\>> in <math|\<bbb-R\>> is
    <math|\<bbb-Q\>>-algebraic (resp. <math|\<bbb-Q\>>-transcendental) if and
    only if it is algebraic (resp. transcendental) in the usual sense.
  </example>

  For <math|\<bbb-F\>> a subfield of <math|\<bbb-K\>>, and
  <math|\<alpha\>\<in\>\<bbb-K\>>, the set
  <math|\<bbb-F\><around*|[|\<alpha\>|]>> (recall the definition from Example
  2.22) is an integral domain since it is a subring of a field, but in
  general <math|\<bbb-F\><around*|[|\<alpha\>|]>> is not a field. We write
  <math|\<bbb-F\><around*|(|\<alpha\>|)>> for
  <math|Frac<rsub|\<bbb-K\>>(\<bbb-F\>[\<alpha\>])>, the field of fractions
  of <math|\<bbb-F\><around*|[|\<alpha\>|]>>, and call it the <strong|field
  <math|\<bbb-F\>> adjoined by <math|\<alpha\>>> \U we `construct
  <math|\<bbb-F\><around*|(|\<alpha\>|)>> by adjoining <math|\<alpha\>> to
  <math|\<bbb-F\>>', e.g. <math|\<bbb-R\><around*|(|i|)>=\<bbb-C\>>,
  <math|\<bbb-Q\><around*|(|<sqrt|2>|)>=\<bbb-Q\>+<sqrt|2>\<bbb-Q\>>.

  <\example>
    The field <math|\<bbb-Q\><around*|(|<sqrt|2>+<sqrt|3>|)>> is certainly
    contained in <math|\<bbb-Q\>+<sqrt|2>\<bbb-Q\>+<sqrt|3>\<bbb-Q\>+<sqrt|6>\<bbb-Q\>>
    which is a ring by the subring test and hence an integral domain. This
    ring contains <math|\<bbb-Q\>> as a subfield and so has an induced
    <math|\<bbb-Q\>>-vector space structure in which it is (at most)
    4-dimensional \U in particular it is finite dimensional \U and so by
    Proposition 1.33 in fact it is a field, and hence
    <math|\<bbb-Q\><around*|(|<sqrt|2>+<sqrt|3>|)>> is a field extension of
    <math|\<bbb-Q\>> of degree at most 4.
  </example>

  <\theorem>
    <dueto|Tower Law>Suppose that <math|\<bbb-K\>> is a field extension of
    <math|\<bbb-L\>> and <math|\<bbb-L\>> is a field extension of
    <math|\<bbb-F\>>. Then <math|\<bbb-K\>> is a field extension of
    <math|\<bbb-F\>>, and if either <math|<around*|\||\<bbb-L\>\<over\>\<bbb-F\>|\|>\<less\>\<infty\>><math|>
    or <math|<around*|\||\<bbb-L\>\<over\>\<bbb-K\>|\|><around*|\||\<bbb-K\>\<over\>\<bbb-F\>|\|>\<less\>\<infty\>>
    then <math|<around*|\||\<bbb-L\>\<over\>\<bbb-F\>|\|>=<around*|\||\<bbb-L\>\<over\>\<bbb-K\>|\|><around*|\||\<bbb-K\>\<over\>\<bbb-F\>|\|>>.
  </theorem>

  <\proof>
    The first part is immediate because the relation `is a subfield of' is
    transitive. Let <math|e<rsub|1>,\<ldots\>,e<rsub|n>> be a basis for
    <math|\<bbb-L\>> as a vector space over <math|\<bbb-K\>>, and let
    <math|f<rsub|1>,\<ldots\>,f<rsub|m>> be a basis for <math|\<bbb-K\>> as a
    vector space over <math|\<bbb-F\>>. Now, for <math|x\<in\>\<bbb-L\>>
    there are scalars <math|\<lambda\><rsub|1>,\<ldots\>,\<lambda\><rsub|n>\<in\>\<bbb-K\>>
    such that <math|x=\<lambda\><rsub|1>e<rsub|1>+\<cdots\>+\<lambda\><rsub|n>e<rsub|n>>,
    and since <math|f<rsub|1>,\<ldots\>,f<rsub|m>> is spanning, for each
    <math|1\<leqslant\>j\<leqslant\>n> there are scalars
    <math|\<mu\><rsub|1,j >,\<ldots\>,\<mu\><rsub|m,j>\<in\>\<bbb-F\>> such
    that <math|\<lambda\><rsub|j>=\<mu\><rsub|1,j>f<rsub|1>+\<cdots\>+\<mu\><rsub|m,j>f<rsub|m>>.
    Hence <math|x=<big|sum><rsup|n><rsub|j=1><big|sum><rsup|m><rsub|i=1>\<mu\><rsub|i,j>f<rsub|i>e<rsub|j>>,
    so we have that <math|(f<rsub|i>e<rsub|j>)<rsup|m,n><rsub|i=1,j=1>> is an
    <math|\<bbb-F\>>-spanning subset of <math|\<bbb-K\>>. Now suppose
    <math|\<mu\><rsub|1,1>,\<ldots\>,\<mu\><rsub|m,n>\<in\>\<bbb-F\>> are
    such that <math|<big|sum><rsup|n><rsub|j=1><big|sum><rsup|m><rsub|i=1>\<mu\><rsub|i,j>f<rsub|i>e<rsub|j>=0<rsub|\<bbb-L\>>>.
    Then <math|<big|sum><rsup|n><rsub|j=1>(<big|sum><rsup|m><rsub|i=1>\<mu\><rsub|i,j>f<rsub|i>)e<rsub|j>=0<rsub|\<bbb-L\>>>,
    but <math|<big|sum><rsup|m><rsub|i=1>\<mu\><rsub|i,j>f<rsub|i>\<in\>\<bbb-K\>>
    for each <math|1\<leqslant\>j\<leqslant\>n> and since
    <math|e<rsub|1>,\<ldots\>,e<rsub|n>> are <math|\<bbb-K\>>-linearly
    independent we have <math|<big|sum><rsup|m><rsub|i=1>\<mu\><rsub|i,j>f<rsub|i>=0<rsub|\<bbb-K\>>>
    for all <math|1\<leqslant\>j\<leqslant\>n>. But now
    <math|f<rsub|1>,\<ldots\>,f<rsub|m>> are <math|\<bbb-F\>>-linearly
    independent and so <math|\<mu\><rsub|i,j>=0<rsub|\<bbb-F\>>> for all
    <math|1\<leqslant\>i\<leqslant\>m> and
    <math|1\<leqslant\>j\<leqslant\>n>. It follows that
    <math|(f<rsub|i>e<rsub|j>)<rsup|m,n><rsub|i=1,j=1>> is a basis for
    <math|\<bbb-L\>> as an <math|\<bbb-F\>>-vector space and the result
    follows.
  </proof>

  <\remark>
    If <math|\<bbb-F\>> is a finite field, and
    <math|<around*|\||\<bbb-K\>\<over\>\<bbb-F\>|\|>=n,<around*|\||\<bbb-L\>\<over\>\<bbb-K\>|\|>=m,>
    and <math|<around*|\||\<bbb-L\>\<over\>\<bbb-F\>|\|>=k> then
    <math|<around*|\||\<bbb-K\>|\|>=<around*|\||\<bbb-F\>|\|><rsup|n>,<around*|\||\<bbb-L\>|\|>=<around*|\||\<bbb-K\>|\|><rsup|m>,>
    and <math|<around*|\||\<bbb-L\>|\|>=<around*|\||\<bbb-F\>|\|><rsup|k>>
    from which it follows that <math|k=n*m>. The proof above is really just
    the observation that we only need to use the `relative size of
    <math|\<bbb-F\>> in <math|\<bbb-K\>>'.
  </remark>

  <\example>
    <dueto|Example 2.39, contd.>The field <math|\<bbb-Q\>(<sqrt|2>+<sqrt|3>)>
    contains <math|<sqrt|2>=<frac|1|2>((<sqrt|2>+<sqrt|3>)<rsup|3>\<minus\>9(<sqrt|2>+<sqrt|3>))>,
    and hence also contains <math|<sqrt|3>>. Now,
    <math|<sqrt|3>\<notin\>\<bbb-Q\>(<sqrt|2>)>. Indeed, suppose for a
    contradiction that there were <math|a,b\<in\>\<bbb-Q\>> with
    <math|<sqrt|3>=a+b<sqrt|2>>. Then squaring both sides and using the
    irrationality of <math|<sqrt|2>> (which exactly says that <math|1> and
    <math|<sqrt|2>> are rationally independent), we have <math|2a*b=0>. But
    <math|b\<neq\>0> since <math|<sqrt|3>> is irrational; and
    <math|a\<neq\>0> since <math|<sqrt|3>/<sqrt|2>> is irrational. We have a
    contradiction.

    By the Tower Law <math|<around*|\||\<bbb-Q\>(<sqrt|2>+<sqrt|3>):\<bbb-Q\>(<sqrt|2>)|\|><around*|\||\<bbb-Q\>(<sqrt|2>):\<bbb-Q\>|\|>=<around*|\||\<bbb-Q\>(<sqrt|2>+<sqrt|3>):\<bbb-Q\>|\|>\<leqslant\>4>.
    However, <math|<around*|\||\<bbb-Q\>(<sqrt|2>):\<bbb-Q\>|\|>\<geqslant\>2>,
    since <math|<sqrt|2>\<notin\>\<bbb-Q\>>; and
    <math|<around*|\||\<bbb-Q\>(<sqrt|2>+<sqrt|3>):\<bbb-Q\>(<sqrt|2>)|\|>\<geqslant\>2>
    since <math|<sqrt|3>\<notin\>\<bbb-Q\>(<sqrt|2>)>. Hence both of these
    extensions are of degree exactly <math|2>, and
    <math|<around*|\||\<bbb-Q\>(<sqrt|2>+<sqrt|3>):\<bbb-Q\>|\|>> is
    <math|4>.
  </example>

  <section|Divisibility>

  Divisibility in <math|\<bbb-Z\>> is a mysterious relation of intrinsic
  mathematical interest as well as wider importance. It is similar to
  divisibility in rings of the form <math|\<bbb-F\>[X]>, and in this section
  we look to understand the source of these similarities.

  In a commutative ring <math|R> we say <math|a> is a <strong|divisor> of
  <math|b>, or <math|a> <strong|divides> <math|b>, or <math|b> is a
  <strong|multiple> of <math|a>, and write <math|a\<divides\>b>, if there is
  <math|x\<in\>R> such that <math|b=a*x(=x*a)>; or, equivalently, if
  <math|b\<in\>\<langle\>a\<rangle\>>; or, equivalently, if
  <math|\<langle\>b\<rangle\>\<subset\>\<langle\>a\<rangle\>>.

  <\observation>
    If <math|a\<divides\>b<rsub|1>,\<ldots\>,b<rsub|n>>, and
    <math|x<rsub|1>,\<ldots\>,x<rsub|n>,y<rsub|1>,\<ldots\>,y<rsub|n>\<in\>R>
    then <math|a\<divides\>x<rsub|1>b<rsub|1>y<rsub|1>+\<cdots\>+x<rsub|n>b<rsub|n>y<rsub|n>>.
    The relation \<divides\> is reflexive and transitive \U relations that
    are reflexive and transitive are sometimes called preorders, and we shall
    think of divisibility with the language of order in mind. When
    <math|a\<divides\>b> <em|and> <math|b\<divides\>a> <em|i.e.>
    <math|<around*|\<langle\>|a|\<rangle\>>=<around*|\<langle\>|b|\<rangle\>>>,
    we say that <math|a> and <math|b> are <strong|associates> and write
    <math|a\<sim\>b>; \<sim\> is an equivalence relation.
  </observation>

  <\example>
    Divisibility in fields is very simple: all elements divide zero, and
    every non-zero element divides every other non-zero element, and so all
    non-zero elements are associates.
  </example>

  <\lemma>
    Suppose that <math|R> is an integral domain. Then

    (i) for all <math|x\<in\>R<rsup|\<ast\>>>, <math|x*a\<divides\>x*b> if
    and only if <math|a\<divides\>b>;

    (ii) <math|a\<sim\>b> if and only if there is <math|u\<in\>U(R)> such
    that <math|a=b*u>.
  </lemma>

  <\proof>
    For (i) the `if' is immediate. To prove the `only if' suppose
    <math|x*a\<divides\>x*b>. Then there is <math|z\<in\>R> such that
    <math|x(a*z)=(x*a)z=x*b>. <math|x\<neq\>0> and so left multiplication by
    <math|x> is injective, and <math|a*z=b> <em|i.e.> <math|a\<divides\>b>.

    For (ii), again the `if' part is immediate. To prove the `only if'
    suppose <math|a\<sim\>b>. Then <math|a\<divides\>b> and
    <math|b\<divides\>a>, so there are <math|v,w\<in\>R> such that
    <math|a*v=b> and <math|b*w=a>, and hence <math|b(w*v)=(b*w)v=a*v=b=b*1>.
    If <math|b\<neq\>0> then left multiplication by <math|b> is injective and
    <math|1=w*v(= v*w)> so <math|w\<in\>U(R)> and we may take <math|u=w>; if
    <math|b=0> then <math|a=0>, and we may take <math|u> to be any unit.
  </proof>

  <\remark>
    The commutative rings where (i) holds are exactly the integral domains,
    since if <math|R> is a commutative ring that is not an integral domain
    then there are <math|x,a\<in\>R<rsup|\<ast\>>> with <math|x*a=0>, and so
    <math|x*a\<divides\>x*0>, but <math|a\<ndivides\>0>.

    Commutative rings where (ii) holds are sometimes called associator rings.
    Exercise I.6 gives examples of integral domains that are not associator
    rings, and associator rings that are not integral domains.
  </remark>

  <subsection|Irreducibles, primes, and uniqueness of factorisation>

  We say that <math|x\<in\>R> is <strong|irreducible> if <math|x\<nsim\>1>
  and whenever <math|a\<divides\>x> we have <math|a\<sim\>x> or
  <math|a\<sim\>1>; or, equivalently, if <math|\<langle\>x\<rangle\>> is
  maximal amongst proper <em|principal> ideals. In particular, if
  <math|y\<sim\>x> and <math|x> is irreducible then <math|y> is also
  irreducible.

  <\remark>
    <with|font|Segoe UI Emoji|\<#26A0\>>0 is sometimes explicitly excluded
    from being irreducible. If 0 is irreducible in the sense above, then in
    fact <math|R> is a field: For <math|x\<in\>R<rsup|\<ast\>>> we have
    <math|\<langle\>x\<rangle\>\<supsetneq\>\<langle\>0\<rangle\>>, and so by
    the maximality of <math|\<langle\>0\<rangle\>> amongst proper principal
    ideals, we conclude that <math|\<langle\>x\<rangle\>> is not proper
    <em|i.e.> <math|\<langle\>x\<rangle\>=R>. Hence there is <math|y\<in\>R>
    with <math|1=x*y(= y*x)>, meaning <math|x\<in\>U(R)>.
  </remark>

  <\example>
    <with|font|Segoe UI Emoji|\<#26A0\>>Irreducible elements can have
    unexpected behaviours: <math|2\<equiv\>2\<times\>2\<times\>2 (mod 6)> but
    2 is irreducible in <math|\<bbb-Z\><rsub|6>> (the ideal does not contain
    3, and so is proper, and has index 2, so by Lagrange's Theorem is
    maximal.)
  </example>

  <\example>
    The irreducible positive integers in <math|\<bbb-Z\>> are exactly the
    prime numbers, and hence the irreducible integers are those of the form
    <math|\<pm\>p> for <math|p> a prime number.
  </example>

  <\example>
    <dueto|Example 1.32, contd.>The algebraic integers
    <math|<wide|\<bbb-Z\>|\<wide-bar\>>> are a non-trivial commutative ring
    containing no irreducible elements. (Exercise II.4 asks for a proof.)
  </example>

  We say that an element <math|x\<in\>R> is <strong|prime> if
  <math|x\<nsim\>1>, and <math|x\<divides\>a*b> implies <math|x\<divides\>a>
  or <math|x\<divides\>b>. In the language of ideals
  <math|\<langle\>x\<rangle\>> is a prime ideal.

  <\observation>
    By induction if <math|x> is prime and
    <math|x\<divides\><big|prod><rsub|i\<in\>I>b<rsub|i>> then there is
    <math|i\<in\>I> such that <math|x\<divides\>b<rsub|i>>.
  </observation>

  <\example>
    <with|font|Segoe UI Emoji|\<#26A0\>>In the ring <math|\<bbb-Z\>> this
    replaces any previous definition of prime, though we shall see later that
    a positive integer is prime in the old sense if and only if it is prime
    in the new sense.

    The integer 2 is prime because i) it is <em|not> either 1 or \<minus\>1;
    and ii) if <math|2\<divides\>a*b> \U in words, if <math|a*b> is even \U
    then <math|2\<divides\>a> or <math|2\<divides\>b> \U in words, at least
    one of <math|a> or <math|b> is even.

    The integer 0 is prime because i) it is <em|not> either 1 or \<minus\>1;
    and ii) if <math|0\<divides\>a*b> then in fact <math|0=a*b> and so either
    <math|0=a>, which can be rewritten as <math|0\<divides\>a>, or
    <math|0=b>, which can be rewritten as <math|0\<divides\>b>. This is the
    special case in the integers of the fact in Proposition 2.28 that a ring
    is an integral domain if and only if <math|0<rsub|R>> is prime.
  </example>

  <\example>
    For <math|R> an integral domain and <math|\<alpha\>\<in\>R>, if
    <math|X\<minus\>\<alpha\>\<divides\>f(X)g(X)> then
    <math|f(\<alpha\>)g(\<alpha\>)=0> and hence either <math|f(\<alpha\>)=0>
    and <math|X\<minus\>\<alpha\>\<divides\>f(X)> by the Factor Theorem, or
    <math|g(\<alpha\>)=0> and similarly <math|X\<minus\>\<alpha\>\<divides\>g(X)>.
    Since <math|X\<minus\>\<alpha\>\<nsim\>1> we have that it is prime.
  </example>

  <\proposition>
    Suppose that <math|R> is an integral domain. Then <math|r\<in\>R> is
    prime as an element of <math|R>, if and only if <math|r> is prime as an
    element of <math|R[X]>.
  </proposition>

  <\proof>
    First <math|U(R)=U(R[X])> and so <math|r\<nsim\>1> in <math|R> if and
    only if <math|r\<nsim\>1> in <math|U(R[X])>.

    Suppose <math|r> is prime in <math|R[X]>, and that <math|r\<divides\>a*b>
    in <math|R>. If either <math|a> or <math|b> is 0 then without loss of
    generality <math|a=0>. Since <math|r\<divides\>a*b=0> we have <math|r=0>,
    and hence <math|r\<divides\>a>. Thus we may restrict attention to the
    case when <math|r\<divides\>a*b> for <math|a,b\<in\>R<rsup|\<ast\>>>. By
    primality of <math|r> in <math|R[X]>, without loss of generality
    <math|r\<divides\>a> in <math|R[X]>. Hence there is <math|p(X)\<in\>R[X]>
    such that <math|r*p(X)=a>. Since <math|a\<in\>R<rsup|\<ast\>>> we have
    <math|deg p=deg r+deg p=deg a=0>, and hence <math|r\<divides\>a> in
    <math|R> as required.

    Now suppose that <math|r> is prime in <math|R>, and
    <math|r\<divides\>p*q> in <math|R[X]> with
    <math|p(X)=a<rsub|0>+a<rsub|1>X+\<cdots\>+a<rsub|n>X<rsup|n>> and
    <math|q(X)=b<rsub|0>+b<rsub|1>X+\<cdots\>+b<rsub|m>X<rsup|m>> with
    <math|r\<ndivides\>p> in <math|R[X]> so that there is some minimal
    <math|k\<in\>\<bbb-N\><rsub|0>> such that <math|r\<ndivides\>a<rsub|k>>
    in <math|R>. Suppose that <math|l\<geqslant\>0> and that we have shown
    <math|r\<divides\>b<rsub|j>> in <math|R> for all <math|j\<less\>l>. The
    coefficient of <math|X<rsup|k+l>> in <math|p*q> is

    <\equation*>
      <big|sum><rsub|j=0><rsup|k+l>a<rsub|j>b<rsub|k+l-j>=<big|sum><rsub|j=0><rsup|k-1>a<rsub|j>b<rsub|k+l-j>+a<rsub|k>b<rsub|l>+<big|sum><rsup|l-1><rsub|j=0>a<rsub|k+l-j>b<rsub|j>
    </equation*>

    <math|r> divides the left hand side (in <math|R>) by hypothesis; it
    divides the first summand on the right (in <math|R>) since
    <math|r\<divides\>a<rsub|i>> in <math|R> for all
    <math|0\<leqslant\>i\<less\>k> by minimality of <math|k>; and it divides
    the last summand (in <math|R>) since <math|r\<divides\>b<rsub|j>> in
    <math|R> for all <math|0\<leqslant\>j\<less\>l> by the inductive
    hypothesis. It follows that <math|r\<divides\>a<rsub|k>b<rsub|l>> in
    <math|R>. But <math|r> is prime in <math|R> and
    <math|r\<ndivides\>a<rsub|k>> in <math|R> by hypothesis, so we conclude
    <math|r\<divides\>b<rsub|l>> in <math|R>. Thus by induction
    <math|r\<divides\>b<rsub|l>> in <math|R> for all
    <math|l\<in\>\<bbb-N\><rsub|0>> so that <math|r\<divides\>q> in
    <math|R[X]> as required.
  </proof>

  <\remark>
    <with|font|Segoe UI Emoji|\<#26A0\>>This does <em|not> just follow
    because <math|R> is a subring of <math|R[X]>: every integral domain is a
    subring of a field, and the only prime in a field is 0, since all
    non-zero elements of a field are units. See Example 3.40.
  </remark>

  Primes are particularly important because they ensure a uniqueness of
  factorisation. To be precise a (possibly empty) vector
  <math|(x<rsub|1>,\<ldots\>,x<rsub|r>)> is a <strong|factorisation> of an
  element <math|x> if <math|x\<sim\>x<rsub|1>\<cdots\>x<rsub|r>>. The
  <math|x<rsub|i>>s are called the <strong|factors>, and if all the factors
  are irreducible then we say that <math|x> has a <strong|factorisation into
  irreducibles>. We say that a factorisation
  <math|(x<rsub|1>,\<ldots\>,x<rsub|r>)> of <math|x> into irreducibles is
  <strong|unique> if whenever <math|(y<rsub|1>,\<ldots\>,y<rsub|s>)> is a
  factorisation of <math|x> into irreducibles there is a bijection
  <math|\<pi\>:{1,\<ldots\>,r}\<rightarrow\>{1,\<ldots\>,s}> such that
  <math|x<rsub|i>\<sim\>y<rsub|\<pi\>(i)>> for all
  <math|1\<leqslant\>i\<leqslant\>r>. <with|font|Segoe UI Emoji|\<#26A0\>>In
  particular, every unit has a unique factorisation into irreducibles with
  the convention that the empty product is <math|1<rsub|R>>.

  <\proposition>
    Suppose that <math|R> is an integral domain and
    <math|x\<in\>R<rsup|\<ast\>>> has a (possibly empty) factorisation in
    which every factor is prime. Then any factorisation of <math|x> into
    irreducibles is unique.
  </proposition>

  <\proof>
    Let <math|(x<rsub|1>,\<ldots\>,x<rsub|r>)> be a factorisation of <math|x>
    in which every factor is prime. We shall prove that if
    <math|(y<rsub|i>)<rsub|i\<in\>I>> are non-zero irreducible elements
    indexed by a finite set <math|I> such that
    <math|x\<sim\><big|prod><rsub|i\<in\>I>y<rsub|i>> then there is a
    bijection <math|\<pi\>:{1,\<ldots\>,r}\<rightarrow\>I> such that
    <math|x<rsub|i>\<sim\>y<rsub|\<pi\>(i)>> for all
    <math|1\<leqslant\>i\<leqslant\>r>, and by transitivity of association
    the result follows.

    We proceed by induction on <math|r>. For <math|r=0> we have
    <math|<big|prod><rsub|i\<in\>I>y<rsub|i>\<sim\>1> (by definition of the
    empty product) and so there is <math|u\<in\>U(R)> such that
    <math|<big|prod><rsub|i\<in\>I>y<rsub|i>=u>. Hence for all
    <math|j\<in\>I>, we have <math|y<rsub|j>(u<rsup|\<minus\>1><big|prod><rsub|i\<in\>I\<setminus\>{j}>y<rsub|i>)=1>
    and so <math|y<rsub|j>\<in\>U(R)>. It follows that <math|I> is empty
    since no unit is irreducible, and we have the base case.

    Now, suppose that <math|r\<gtr\>0>. Then <math|x<rsub|r>> is prime and
    <math|x<rsub|r>\<divides\><big|prod><rsub|i\<in\>I>y<rsub|i>>. By
    primality there is some <math|j\<in\>I> such that
    <math|x<rsub|r>\<divides\>y<rsub|j>>. But <math|y<rsub|j>> is irreducible
    and <math|x<rsub|r>\<nsim\>1> and so <math|x<rsub|r>\<sim\>y<rsub|j>>.
    Cancelling <math|y<rsub|j>> we get <math|x<rsub|1>\<cdots\>x<rsub|r\<minus\>1>\<sim\><big|prod><rsub|i\<in\>I\<setminus\>{j}>y<rsub|i>>
    and by the inductive hypothesis there is a bijection
    <math|<wide|\<pi\>|~>:{1,\<ldots\>,r\<minus\>1}\<rightarrow\>I\<setminus\>{j}>
    such that <math|x<rsub|i>\<sim\>y<rsub|<wide|\<pi\>|~>(i)>> for all
    <math|1\<leqslant\>i\<leqslant\>r\<minus\>1>. Extend this to a bijection
    <math|\<pi\>:{1,\<ldots\>,r}\<rightarrow\>I> by setting
    <math|\<pi\>(r)=j> and the result is proved.
  </proof>

  <\proposition>
    Suppose that <math|R> is an integral domain and
    <math|x\<in\>R<rsup|\<ast\>>> is prime. Then <math|x> is irreducible.
  </proposition>

  <\proof>
    First, <math|x\<nsim\>1>. Now suppose that <math|a\<divides\>x>. Then
    there is <math|b\<in\>R> such that <math|x=a*b>, and <math|b\<neq\>0>
    since <math|x\<neq\>0>. By primality of <math|x> either
    <math|x\<divides\>a> and so <math|x\<sim\>a>; or
    <math|a*b=x\<divides\>b>, but <math|b\<neq\>0> and so
    <math|a\<divides\>1>, and hence <math|a\<sim\>1> (since certainly
    <math|1\<divides\>a>).
  </proof>

  <\example>
    <dueto|Example 3.11, contd.>For <math|R> an integral domain we saw that
    the polynomials <math|X\<minus\>\<alpha\>> are prime in <math|R[X]>, but
    then <math|R[X]> is an integral domain and so <math|X\<minus\>\<alpha\>>
    is irreducible by the above.
  </example>

  <\example>
    2 is an irreducible element of <math|\<bbb-Z\>[<sqrt|-5>]> that is not
    prime; Exercise \<#2161\>.2 asks for a proof.

    <with|font|Segoe UI Emoji|\<#26A0\>>The ideal
    <math|<around*|\<langle\>|X<around*|(|mod 2X|)>|\<rangle\>>> is prime in
    the commutative ring <math|R=\<bbb-Z\><around*|[|X|]>/<around*|\<langle\>|2X|\<rangle\>>>,
    but it is not irreducible. Of course <math|R> is <em|not> an integral
    domain! For the former claim, the map
    <math|R\<rightarrow\>\<bbb-Z\>;p<around*|(|X|)><around*|(|mod
    2X|)>\<mapsto\>p<around*|(|0|)>> is a well-defined surjective ring
    homomorphism with kernel <math|<around*|\<langle\>|X<around*|(|mod
    2X|)>|\<rangle\>>>, and <math|\<bbb-Z\>> is an integral domain so the
    kernel is prime by the First Isomorphism Theorem; for the latter
    <math|<around*|\<langle\>|3<around*|(|mod 2X|)>|\<rangle\>>> is a proper
    principal ideal in <math|R> which properly contains
    <math|<around*|\<langle\>|X<around*|(|mod 2X|)>|\<rangle\>>>.
  </example>

  In the integers (as we shall see shortly) the converse holds as a
  consequence of Bezout's Lemma, and we make a definition which captures
  rings in which Bezout's Lemma holds: we say that an integral domain
  <math|R> is a <strong|Bezout domain> if every finitely generated ideal is
  principal.

  <\example>
    The ring of integers, <math|\<bbb-Z\>>, is a Bezout domain since every
    ideal is principal, so in particular every finitely generated ideal in
    principal. However, the connection with Bezout's Lemma is closer: in the
    language of ideals this states that any ideal in <math|\<bbb-Z\>> that is
    generated by two elements can also be generated by one element <em|i.e.>
    is principal, and by induction that any finitely generated ideal in
    <math|\<bbb-Z\>> is principal.
  </example>

  <\example>
    The algebraic integers <math|<wide|\<bbb-Z\>|\<wide-bar\>>> is a Bezout
    domain. A proof may be found in [Kap70, Theorem 102] though the
    prerequisites are considerable.
  </example>

  <\example>
    <math|\<bbb-Z\>[X]> is an example of an integral domain that is not a
    Bezout domain because (as we saw in Example 2.12)
    <math|\<langle\>2,X\<rangle\>> is finitely generated but not principal.
  </example>

  <\proposition>
    Suppose that <math|R> is a Bezout domain and <math|x\<in\>R> is
    irreducible. Then <math|x> is prime.
  </proposition>

  <\proof>
    Suppose <math|x\<divides\>a*b> and let <math|d> be a generator of the
    ideal <math|\<langle\>x,b\<rangle\>>. Then <math|d\<divides\>x>, and
    since <math|x> is irreducible either <math|d\<sim\>x> or
    <math|d\<sim\>1>. Since we also have <math|d\<divides\>b>, if
    <math|d\<sim\>x> then <math|x\<divides\>d\<divides\>b>. On the other
    hand, if <math|d\<sim\>1> then there are elements <math|u,v\<in\>R> such
    that <math|1=u*x+b*v>. Multiplying by <math|a> we have
    <math|a*u*x+a*b*v=a>, but <math|x\<divides\>a*u*x> and
    <math|x\<divides\>a*b*v>, and so <math|x\<divides\>a> as required.
  </proof>

  <\proposition>
    Suppose that <math|R> is a Bezout domain. Then for every pair
    <math|a,b\<in\>R> there is <math|d> and <math|l> with <math|a*b=l*d>, and
    <math|\<langle\>a\<rangle\>+\<langle\>b\<rangle\>=\<langle\>d\<rangle\>>,
    and <math|\<langle\>a\<rangle\>\<cap\>\<langle\>b\<rangle\>=\<langle\>l\<rangle\>>.
  </proposition>

  <\proof>
    Since every finitely generated ideal in <math|R> is principal there is
    some <math|d\<in\>R> such that <math|\<langle\>a\<rangle\>+\<langle\>b\<rangle\>=\<langle\>a,b\<rangle\>=\<langle\>d\<rangle\>>.
    Let <math|x,y\<in\>R> be such that <math|d=x*a+b*y>, and
    <math|z,w\<in\>R> be such that <math|b=z*d> and <math|a=d*w>; put
    <math|l\<assign\>z*d*w> and note <math|a*b=l*d>.

    Now, <math|l=b*w\<in\>\<langle\>b\<rangle\>> and
    <math|l=z*a\<in\>\<langle\>a\<rangle\>>, so
    <math|l\<in\>\<langle\>a\<rangle\>\<cap\>\<langle\>b\<rangle\>>. On the
    other hand if <math|m\<in\>\<langle\>a\<rangle\>\<cap\>\<langle\>b\<rangle\>>
    then <math|a,b\<divides\>m> so <math|a*b\<divides\>a*m>, and
    <math|a*b\<divides\>m*b>. Hence <math|l*d=a*b\<divides\>x*a*m+m*b*y=m*d>.
    If <math|d\<neq\>0> then by cancellation we have <math|l\<divides\>m>
    which is to say <math|m\<in\><around*|\<langle\>|l|\<rangle\>>> as
    required. If <math|d=0> then <math|a=b=0>, and so <math|l=0> and we are
    done.
  </proof>

  <\remark>
    The set <math|\<langle\>a\<rangle\>> is the set of multiples of <math|a>,
    and the set <math|\<langle\>b\<rangle\>> is the set of multiples of
    <math|b>, hence <math|\<langle\>a\<rangle\>\<cap\>\<langle\>b\<rangle\>>
    is the set of common multiples of <math|a> and <math|b>, and to say that
    it is generated by <math|l> is exactly to say that there is a common
    multiple of <math|a> and <math|b> that divides all other common multiples
    \U such a common multiple is called a <strong|least common multiple
    (lcm)>.

    On the other hand if <math|\<langle\>a\<rangle\>+\<langle\>b\<rangle\>=\<langle\>d\<rangle\>>,
    then <math|a\<in\>\<langle\>d\<rangle\>> and
    <math|b\<in\>\<langle\>d\<rangle\>> so that <math|d\<divides\>a> and
    <math|d\<divides\>b> <em|i.e.> <math|d> is a common divisor of <math|a>
    and <math|b>. On the other hand there are <math|z,w\<in\>R> with
    <math|d=x*a+b*y>, so if <math|c> is another common divisor of <math|a>
    and <math|b> then <math|c\<divides\>x*a+b*y=d> \U which is to say that
    every common divisor of <math|a> and <math|b> divides <math|d>. Such a
    common divisor is called a <strong|greatest common divisor (gcd)>.
  </remark>

  <subsection|Euclidean domains and division algorithms>

  The process of dividing integers (or polynomials) is captured by the
  division algorithm, and rings where we have such an algorithm will be
  particularly good to work with. A <strong|Euclidean function> on an
  integral domain <math|R> is a function <math|f:R<rsup|\<ast\>>\<rightarrow\>\<bbb-N\><rsub|0>>
  such that

  \<bullet\> <math|f(a)\<leqslant\>f(b)> whenever <math|a\<divides\>b> (both
  non-zero);

  \<bullet\> and if <math|a,b\<in\>R<rsup|\<ast\>>> then either
  <math|b\<divides\>a>, or there are <math|q\<in\>R,r\<in\><math|R<rsup|\<ast\>>>>
  such that <math|a=b*q+r> and <math|f(r)\<less\>f(b)>.

  We say that an integral domain <math|R> is a <strong|Euclidean domain> if
  <math|R> supports at least one Euclidean function.

  <\remark>
    <with|font|Segoe UI Emoji|\<#26A0\>>Keating [Kea98, p17] uses an even
    stronger definition of Euclidean function <math|f> requiring that
    <math|f(a*b)=f(a)f(b)> whenever <math|a,b\<in\>R<rsup|\<ast\>>*>. This is
    a genuinely stronger definition, meaning there are Euclidean domains in
    our sense but not in the sense of Keating, though this is a recent
    discovery: [CNT19, Theorem 1.3].
  </remark>

  <\example>
    Let <math|f:\<bbb-F\><rsup|\<ast\>>\<rightarrow\>\<bbb-N\><rsub|0>> be
    the constant function 1. Since <math|f(a)=f(b)> for all <math|a> and
    <math|b>, and every two non-zero units divide each other in a field,
    <math|f> is a Euclidean function for <math|\<bbb-F\>> and so
    <math|\<bbb-F\>> is a Euclidean domain.
  </example>

  <\example>
    If <math|a,b\<in\>\<bbb-Z\><rsup|\<ast\>>> and <math|b\<ndivides\>a>,
    pick <math|r\<in\><around*|{|a-b*q:q\<in\>\<bbb-Z\>|}>> such that
    <math|<around*|\||r|\|>> is smallest, then
    <math|<around*|\||r|\|>\<less\><around*|\||b|\|>>, and
    <math|<around*|\||\<cdot\>|\|>> is a Euclidean function on
    <math|\<bbb-Z\>> and <math|\<bbb-Z\>> is a Euclidean domain. (It
    certainly has <math|<around*|\||a|\|>\<leqslant\><around*|\||b|\|>>
    whenever <math|a\<divides\>b>.)
  </example>

  <\example>
    If <math|a,b\<in\>\<bbb-F\><around*|[|X|]><rsup|\<ast\>>> and
    <math|b\<ndivides\>a> then <math|a-b q> is not the zero polynomial for
    any <math|q\<in\>\<bbb-F\><around*|[|X|]>>, and we can pick <math|b q>
    such that <math|a-b q> has smallest possible degree. Then
    <math|r\<assign\>a+b*q> has <math|deg r\<less\>deg b>, since otherwise
    writing <math|\<lambda\>> for the ratio between the lead coefficient of
    <math|r> and that of <math|b> we have
    <math|r(X)\<minus\>\<lambda\>X<rsup|deg r\<minus\>deg b>b(X)> of the form
    <math|a\<minus\>b*q<rprime|'>> and of strictly smaller degree than
    <math|r>. Finally, <math|deg p\<leqslant\>deg q> whenever
    <math|p\<divides\>q>, and so deg is a Euclidean function and
    <math|\<bbb-F\>[X]> is a Euclidean domain.
  </example>

  An integral domain in which every ideal is principal is called a
  <strong|principal ideal domain (PID)>. In particular, every PID is <em|a
  fortiori> a Bezout domain so all the work of the previous section applies
  to PIDs.

  <\proposition>
    Suppose that <math|R> is a Euclidean domain. Then <math|R> is a PID.
  </proposition>

  <\proof>
    Let <math|f> be a Euclidean function on <math|R> and suppose <math|I> is
    a non-zero ideal. Let <math|x\<in\>I> have <math|f<around*|(|x|)>>
    minimal, and suppose that <math|y\<in\>I>. If
    <math|y\<nin\><around*|\<langle\>|x|\<rangle\>>> then there is
    <math|q\<in\>R> and <math|r\<in\>R<rsup|\<ast\>>> with <math|y=q x+r> and
    <math|f<around*|(|r|)>\<less\>f<around*|(|x|)>> so that <math|r\<in\>I>,
    contradicting minimality of <math|f<around*|(|x|)>>.
  </proof>

  <\remark>
    The ring <math|\<bbb-Z\>[\<theta\>]> (where
    <math|\<theta\><rsup|2>\<minus\>\<theta\>+5=0>) is an example of <hlink|a
    PID that is not a Euclidean domain|https://webspace.maths.qmul.ac.uk/r.a.wilson/MTH5100/PIDnotED.pdf>,
    though in view of Exercise II.9 we shall not treat them very differently;
    a proof may be found in [Con, Theorem 5.13].
  </remark>

  <subsection|The ACCP and unique factorisation domains>

  Other than Bezout's lemma, the integers enjoy another important property:
  we cannot `keep dividing indefinitely', and this is what ensures the
  existence of factorisations into primes.

  An integral domain <math|R> has the <strong|ascending chain condition on
  principal ideals> or <strong|ACCP> if for every sequence
  <math|(d<rsub|n>)<rsup|\<infty\>><rsub|n=0>> of elements with
  <math|d<rsub|n+1>\<divides\>d<rsub|n>> for all
  <math|n\<in\>\<bbb-N\><rsub|0>>, there is some
  <math|N\<in\>\<bbb-N\><rsub|0>> such that <math|d<rsub|n>\<sim\>d<rsub|N>>
  for all <math|n\<geqslant\>N>.

  <\proposition*>
    A Bezout domain <math|R> has the ACCP. Then <math|R> is a PID.
  </proposition*>

  <\proof>
    Let <math|I> be a non-principal ideal, <math|x<rsub|0>\<in\>I>,
    <math|\<exists\>y<rsub|1>\<in\>I\<setminus\><around*|{|x<rsub|0>|}>>. By
    Bezout <math|\<exists\>x<rsub|1>> such that
    <math|<around*|\<langle\>|x<rsub|1>|\<rangle\>>=<around*|\<langle\>|y<rsub|1>,x<rsub|0>|\<rangle\>>>.
    Then <math|x<rsub|1>\<divides\>x<rsub|0>> and
    <math|x<rsub|1>\<nsim\>x<rsub|0>>, <math|x<rsub|1>\<in\>I>. Now repeat
    with <math|x<rsub|1>> to get <math|x<rsub|2>> etc. This gives
    <math|\<cdots\>\<divides\>x<rsub|2>\<divides\>x<rsub|1>\<divides\>x<rsub|0>>
    such that <math|x<rsub|i>\<nsim\>x<rsub|i+1>\<forall\>i>, contradicting
    the ACCP.
  </proof>

  <\proposition>
    Suppose that <math|R> is a PID. Then <math|R> has the ACCP.
  </proposition>

  <\proof>
    Suppose that <math|(d<rsub|n>)<rsup|\<infty\>><rsub|n=0>> has
    <math|d<rsub|n+1>\<divides\>d<rsub|n>> for all
    <math|n\<in\>\<bbb-N\><rsub|0>>, so that
    <math|\<langle\>d<rsub|0>\<rangle\>\<subset\>\<langle\>d<rsub|1>\<rangle\>\<subset\>\<cdots\>>
    and let <math|I=<big|cup><rsub|n\<in\>\<bbb-N\><rsub|0>>\<langle\>d<rsub|n>\<rangle\>>.
    <math|I> is an ideal: If <math|s,t\<in\>I> then there are
    <math|n,m\<in\>\<bbb-N\><rsub|0>> such that
    <math|s\<in\>\<langle\>d<rsub|n>\<rangle\>> and
    <math|t\<in\>\<langle\>d<rsub|m>\<rangle\>> and so
    <math|s,t\<in\>\<langle\>d<rsub|max{n,m}>\<rangle\>> by nesting, and
    hence <math|s\<minus\>t\<in\>\<langle\>d<rsub|max{n,m}>\<rangle\>\<subset\>I>.
    Since <math|0\<in\>I>, it is a subgroup by the subgroup test, and finally
    if <math|r\<in\>R> then <math|r*s,s*r\<in\>\<langle\>d<rsub|n>\<rangle\>\<subset\>I>
    as required.

    Since <math|R> is a PID there is some <math|d\<in\>I> such that
    <math|I=\<langle\>d\<rangle\>>. Since <math|d\<in\>I> there is some
    <math|N\<in\>\<bbb-N\><rsub|0>> such that <math|d<rsub|N>\<divides\>d>,
    but then <math|d<rsub|n>\<in\>I> for all <math|n\<in\>\<bbb-N\><rsub|0>>
    and so <math|d<rsub|N>\<divides\>d\<divides\>d<rsub|n>> for all
    <math|n\<in\>\<bbb-N\><rsub|0>> and hence
    <math|d<rsub|n>\<sim\>d<rsub|N>> for all <math|n\<geqslant\>N>. The
    result is proved.
  </proof>

  <\example>
    The ring of algebraic integers <math|<wide|\<bbb-Z\>|\<wide-bar\>>> does
    not satisfy the ACCP giving an example of a Bezout domain that is not a
    PID. Exercise II.4 develops a proof of this.
  </example>

  <\proposition>
    Suppose that <math|R> is an integral domain with the ACCP. Then every
    <math|x\<in\>R<rsup|\<ast\>>> has a factorisation into irreducibles.
  </proposition>

  <\proof>
    Write <math|\<cal-F\>> for the set of elements in <math|R<rsup|\<ast\>>>
    that have a factorisation into irreducibles so that all units and
    irreducible elements are in <math|\<cal-F\>>. <math|\<cal-F\>> is closed
    under multiplication, by design and since <math|R> is an integral domain.

    Were <math|\<cal-F\>> not to be the whole of <math|R<rsup|\<ast\>>> then
    there would be some <math|x<rsub|0>\<in\>R<rsup|\<ast\>>\<setminus\>\<cal-F\>>.
    Now create a chain iteratively: at step <math|i> suppose we have
    <math|x<rsub|i>\<in\>R<rsup|\<ast\>>\<setminus\>\<cal-F\>>. Since
    <math|x<rsub|i>> is not irreducible and not a unit there is
    <math|y<rsub|i>\<divides\>x<rsub|i>> with <math|y<rsub|i>\<nsim\>1> and
    <math|y<rsub|i>\<nsim\>x<rsub|i>>; let
    <math|z<rsub|i>\<in\>R<rsup|\<ast\>>> be such that
    <math|x<rsub|i>=y<rsub|i>z<rsub|i>>. If <math|z<rsub|i>\<sim\>x<rsub|i>>,
    then <math|z<rsub|i>\<sim\>y<rsub|i>z<rsub|i>> and by cancellation
    <math|1\<sim\>y<rsub|i>>, a contradiction. We conclude
    <math|y<rsub|i>,z<rsub|i>\<nsim\>x<rsub|i>>.

    Since <math|\<cal-F\>> is closed under multiplication we cannot have both
    <math|y<rsub|i>> and <math|z<rsub|i>> in <math|\<cal-F\>>. Let
    <math|x<rsub|i+1>\<in\>{y<rsub|i>, z<rsub|i>}> such that
    <math|x<rsub|i+1>\<notin\>\<cal-F\>>; by design
    <math|x<rsub|i+1>\<divides\>x<rsub|i>> and
    <math|x<rsub|i+1>\<nsim\>x<rsub|i>>. This process produces a sequence
    <math|\<cdots\>\<divides\>x<rsub|2>\<divides\>x<rsub|1>\<divides\>x<rsub|0>>
    in which <math|x<rsub|i>\<nsim\>x<rsub|i+1>> for all
    <math|i\<in\>\<bbb-N\><rsub|0>> contradicting the ACCP.
  </proof>

  <\remark>
    Integral domains in which every non-zero element has a factorisation into
    irreducibles are called <strong|factorisation domains> or <strong|atomic
    domains>. There are factorisation domains not having the ACCP but these
    are not easy to construct; the first example was given by Anne Grams in
    [Gra74].
  </remark>

  Finally, a <strong|unique factorisation domain> or <strong|UFD> is an
  integral domain in which every <math|x\<in\>R<rsup|\<ast\>>> has a unique
  factorisation into irreducibles.

  <\theorem>
    Suppose that <math|R> is a PID. Then <math|R> is a UFD.
  </theorem>

  <\proof>
    Since every PID has the ACCP, Proposition 3.32 tells us that every
    <math|x\<in\>R<rsup|\<ast\>>> has a factorisation into irreducibles. But
    every PID is a Bezout domain, and every irreducible in a Bezout domain is
    prime, and the result follows from Proposition 3.14.
  </proof>

  <\example>
    <math|\<bbb-Z\>[X]> is an example of a UFD that is not a PID; see
    Exercise II.8 for details.
  </example>

  <subsection|Finding irreducibles>

  Irreducible elements of a ring are of interest in the same way that the
  elements (in the sense of the periodic table) are of interest in chemistry:
  they are the building blocks of the non-zero elements (in the sense of
  elements of a set) of the ring.

  In PIDs irreducibles are of even more interest because they generate
  <strong|maximal> ideals: not just maximal amongst principal ideals, but
  maximal amongst <em|all> ideals, because all ideals are principal in a PID.
  This means that the quotient of a PID by the ideal generated by an
  irreducible element produces a field. We have already seen this with the
  primes in <math|\<bbb-Z\>> producing the fields <math|\<bbb-F\><rsub|p>>,
  but there are many more fields arising from quotient rings.

  We begin with a short technical lemma which can help in finding irreducible
  polynomials of degree 2 and 3.

  <\lemma>
    Suppose that <math|R> is an integral domain and <math|f\<in\>R[X]>. Then
    if <math|f> has a root and degree at least 2, it is not irreducible; and
    if <math|f> is monic of degree at most 3 and is not irreducible then it
    has a root.
  </lemma>

  <\proof>
    If <math|f> has a root <math|\<alpha\>> then by the Factor Theorem
    <math|X\<minus\>\<alpha\>> divides <math|f>. Since
    <math|deg(X\<minus\>\<alpha\>)=1> we have
    <math|X\<minus\>\<alpha\>\<nsim\>1>, and since additionally <math|deg
    f\<geqslant\>2> we have <math|X\<minus\>\<alpha\>\<nsim\>f>. We conclude
    that <math|f> is not irreducible.

    If <math|f> has degree at most 3, and <math|g\<divides\>f> has
    <math|g\<nsim\>1> and <math|g\<nsim\>f> then let
    <math|h\<in\>R[X]<rsup|\<ast\>>> be such that <math|f=g*h>. Since
    <math|g,h\<divides\>f>, and <math|f> is monic the lead coefficients of
    <math|g> and <math|h> are both units. Since <math|g\<nsim\>1> we have
    <math|deg g\<gtr\>0>; since <math|g\<nsim\>f> we have <math|deg
    g\<less\>deg f>. But then since <math|3\<geqslant\>deg f=deg g +deg h> we
    have either <math|deg g=1> or <math|deg h=1>. In the first case, since
    the lead coefficient of <math|g> is a unit, <math|g> has a root in
    <math|R>; in the second case similarly <math|h> has a root in <math|R>.

    It follows that <math|f> has a root in <math|R>.
  </proof>

  <\example>
    <math|X<rsup|2>+X+1\<in\>\<bbb-F\><rsub|2>[X]> has no root in
    \<bbb-F\><rsub|2> and is monic, so is irreducible in
    <math|\<bbb-F\><rsub|2>[X]>, so <math|\<bbb-F\><rsub|2><around*|[|X|]>/<around*|\<langle\>|x<rsup|2>+x+1|\<rangle\>>=<around*|{|0,1,x,1+x|}>>
    is a field of characteristic 2, so <math|\<neq\>\<bbb-Z\><rsub|4>>.

    <math|(X<rsup|2>+X+1)<rsup|2>=X<rsup|4>+X<rsup|2>+1> is not irreducible
    but it is also monic and has no root.
  </example>

  <\example>
    The polynomials <math|X<rsup|3>+X<rsup|2>+1> and <math|X<rsup|3>+X+1> are
    the only degree 3 irreducible polynomials in <math|\<bbb-F\><rsub|2>[X]>:
    There are only eight degree 3 polynomials in <math|\<bbb-F\><rsub|2>[X]>
    and the constant term may not be 0, or else 0 is a root. Hence there are
    only four polynomials to consider: <math|X<rsup|3>+X<rsup|2>+X+1,X<rsup|3>+X+1,X<rsup|3>+X<rsup|2>+1,>
    and <math|X<rsup|3>+1>. The first and last of these have 1 as a root, and
    the other two do not.
  </example>

  Every finite field has size a power of a prime (Exercise I.7 asked for a
  proof of this), and we can produce a field of order <math|p<rsup|n>> for
  <math|p> a prime if we can find <math|f\<in\>\<bbb-F\><rsub|p>[X]>
  irreducible of degree <math|n>. A proof that we can find such irreducibles,
  modelled on the proof of Bertrand's postulate, may be found in [Sou20]; for
  now we content ourselves for finding a large class of fields of order
  <math|p<rsup|2>>:

  <\example>
    We call <math|a\<in\>\<bbb-F\><rsub|p>> a <strong|quadratic non-residue>
    if there is no <math|x\<in\>\<bbb-F\><rsub|p>> such that
    <math|x<rsup|2>\<equiv\>a (mod p)>. For example, \<minus\>1 is a
    quadratic non-residue if <math|p> is a prime with <math|p\<equiv\>3 (mod
    4)> because if <math|x\<in\>\<bbb-F\><rsub|p>> had
    <math|x<rsup|2>\<equiv\>\<minus\>1 (mod p)> then
    <math|<around*|\<langle\>|x|\<rangle\>>=<around*|{|1,x,-1,-x|}>> of order
    4 in <math|U(\<bbb-F\><rsub|p>)>. However, <math|U(\<bbb-F\><rsub|p>)>
    has order <math|p\<minus\>1>, which is not divisible by 4, violating
    Lagrange's Theorem.

    When <math|p\<equiv\>3 (mod 4)>, <math|X<rsup|2>+1> is irreducible, and
    hence <math|\<bbb-F\><rsub|p>[X]/\<langle\>X<rsup|2>+1\<rangle\>> is a
    field and it is 2-dimensional in the <math|\<bbb-F\><rsub|p>>-vector
    space structure induced by the quotient map (composed with the inclusion
    of <math|\<bbb-F\><rsub|p>>). In particular, it has size <math|p<rsup|2>>
    and so is not isomorphic to <math|\<bbb-F\><rsub|q>> for any prime
    <math|q> \U these are new fields \U and it is not isomorphic to
    <math|\<bbb-Z\><rsub|p<rsup|2>>> since this is not even an integral
    domain.
  </example>

  The rationals are an infinite field and so checking a polynomial for
  rational roots does not yield to the same brute force approaches that can
  work in finite fields. However, there is a result of Gauss which lets us
  connect irreducibility of polynomials in <math|\<bbb-Z\>[X]>, where we only
  have to check for integer roots, with irreducibility in
  <math|\<bbb-Q\>[X]>.

  <\example>
    <with|font|Segoe UI Emoji|\<#26A0\>><math|2X\<in\>\<bbb-Z\><around*|[|X|]>>
    is not irreducible in <math|\<bbb-Z\>[X]> because <math|2\<divides\>2X>
    and <math|2\<nsim\>1> and <math|2\<nsim\>X>. On the other hand
    <math|2X\<sim\>X> in <math|\<bbb-Q\>[X]>, and so it is irreducible in
    <math|\<bbb-Q\>[X]>.
  </example>

  We say that <math|f\<in\>\<bbb-Z\>[X]> is <strong|primitive> if 1 is a
  greatest common divisor of the coefficients in <math|f>. In particular, if
  <math|f> is primitive and of degree 0 then <math|f> is a unit in
  <math|\<bbb-Z\>[X]>.

  <\theorem>
    <dueto|Gauss' Lemma>Suppose that <math|f\<in\>\<bbb-Z\>[X]>. Then
    <math|f> is non-constant and irreducible in
    <math|\<bbb-Z\><around*|[|X|]>> if and only if <math|f> is primitive and
    irreducible in <math|\<bbb-Q\>[X]>.
  </theorem>

  <\proof>
    Suppose that <math|f> is irreducible in <math|\<bbb-Z\><around*|[|X|]>>.
    This immediately tells us that <math|f> is primitive since it were not
    there would be <math|n\<nsim\>1> such that <math|n\<divides\>f> in
    <math|\<bbb-Z\>[X]>. Since <math|n\<nsim\>1> we conclude that
    <math|n\<sim\>f> (in <math|\<bbb-Z\>[X]>) by irreducibility of <math|f>,
    contradicting the fact that <math|f> is non-constant.

    Now, suppose that <math|f=g*h> for <math|g,h\<in\>\<bbb-Q\>[X]>. Then let
    <math|\<lambda\>\<in\><math|\<bbb-N\><rsup|\<ast\>>>> be minimal such
    that there is <math|q\<in\>\<bbb-Q\><rsup|\<ast\>>> with
    <math|\<lambda\>q<rsup|\<minus\>1>g> and <math|q*h> both in
    <math|\<bbb-Z\>[X]>. Suppose that <math|p\<in\>\<bbb-Z\>> is prime with
    <math|p\<divides\>\<lambda\>>. Then <math|p> is prime as a constant
    polynomial in <math|\<bbb-Z\>[X]> and since
    <math|p\<divides\>\<lambda\>f=(\<lambda\>q<rsup|\<minus\>1>g)(q*h)>, we
    have <math|p\<divides\>\<lambda\>q<rsup|\<minus\>1>g> or
    <math|p\<divides\>q*h> (both in <math|\<bbb-Z\>[X]>). The former
    contradicts minimality of <math|\<lambda\>> directly, and the latter once
    we note that <math|(q/p)h\<in\>\<bbb-Z\>[X]> and
    <math|(\<lambda\>/p)(q/p)<rsup|\<minus\>1>g=\<lambda\>q<rsup|\<minus\>1>g\<in\>\<bbb-Z\>[X]>.
    We conclude that <math|\<lambda\>> has no prime factors and hence (since
    <math|\<bbb-Z\>> is a UFD) is a unit. Thus
    <math|q<rsup|\<minus\>1>g\<divides\>f> in <math|\<bbb-Z\>[X]> and so by
    irreducibility of <math|f> in <math|\<bbb-Z\>[X]> we conclude that either
    <math|q<rsup|\<minus\>1>g\<sim\>1> or <math|q<rsup|\<minus\>1>g\<sim\>f>
    in <math|\<bbb-Z\>[X]>. Hence either <math|g\<sim\>1> in
    <math|\<bbb-Q\>[X]> or <math|g\<sim\>f> in <math|\<bbb-Q\>[X]> and
    finally, since <math|f> is non-constant we have <math|f\<nsim\>1> in
    <math|\<bbb-Q\>[X]> and so <math|f> is irreducible in
    <math|\<bbb-Q\>[X]>.

    Conversely, suppose <math|f\<in\>\<bbb-Z\>[X]> is primitive and
    irreducible in <math|\<bbb-Q\>[X]>. First, <math|f\<nsim\>1> in
    <math|\<bbb-Q\>[X]> and so <math|f> is non-constant. Suppose
    <math|g\<divides\>f> in <math|\<bbb-Z\>[X]>. By irreducibility of
    <math|f> in <math|\<bbb-Q\>[X]>, either <math|g\<sim\>1> in
    <math|\<bbb-Q\>[X]> so <math|deg g=0>, and since <math|f> is primitive
    <math|g\<sim\>1> in <math|\<bbb-Z\>[X]>; or <math|g\<sim\>f> in
    <math|\<bbb-Q\>[X]>, then <math|deg g=deg f> and writing <math|f=g*h> for
    <math|h\<in\>\<bbb-Z\>[X]> we have <math|deg h=0>, and since <math|f> is
    primitive <math|h\<sim\>1> in <math|\<bbb-Z\>[X]>, whence
    <math|g\<sim\>f> in <math|\<bbb-Z\>[X]>. The result is proved.
  </proof>

  <\example>
    The polynomial <math|p(X)=X<rsup|3>+X+1> is non-constant and irreducible
    in <math|\<bbb-Z\>[X]> because it has degree at most 3 and no root in
    <math|\<bbb-Z\>>. Hence it is irreducible in
    <math|\<bbb-Q\><around*|[|X|]>>. <math|\<bbb-Q\><around*|[|X|]>/<around*|\<langle\>|X<rsup|3>+X+1|\<rangle\>>>
    is a degree 3 extension of <math|\<bbb-Q\>>.
  </example>

  <\proposition>
    <dueto|Eisenstein's Criterion>Suppose that
    <math|f<around*|(|X|)>=a<rsub|n>X<rsup|n>+\<cdots\>+a<rsub|1>X+a<rsub|0>>
    is a <strong|primitive> polynomial in <math|\<bbb-Z\><around*|[|X|]>> and
    <math|p> is a prime in <math|\<bbb-Z\>> such that
    <math|p\<divides\>a<rsub|i>> in <math|\<bbb-Z\>> for all
    <math|0\<leqslant\>i\<less\>n>; <math|p\<nmid\>a<rsub|n>>; and
    <math|p<rsup|2>\<nmid\>a<rsub|0>> in <math|\<bbb-Z\>>. Then <math|f> is
    irreducible in <math|\<bbb-Z\><around*|[|X|]>>.
  </proposition>

  <\proof>
    Suppose that <math|f=g*h> for <math|g,h\<in\>\<bbb-Z\><around*|[|X|]>>.
    Write <math|\<phi\>:\<bbb-Z\><around*|[|X|]>\<rightarrow\>\<bbb-F\><rsub|p><around*|[|X|]>>
    for the evaluation homomorphism at <math|X> (<em|i.e.> mapping <math|X>
    to <math|X>) extending the quotient map
    <math|\<bbb-Z\>\<rightarrow\>\<bbb-F\><rsub|p>>. Then

    <\equation*>
      \<phi\><around*|(|f|)>=\<phi\><around*|(|g|)>\<phi\><around*|(|h|)><text|
      and >deg q\<geqslant\>deg \<phi\><around*|(|q|)><text| whenever
      >\<phi\><around*|(|q|)>\<in\>\<bbb-F\><rsub|p><around*|[|X|]><rsup|\<ast\>>.
    </equation*>

    Since <math|p\<divides\>a<rsub|i>> for all <math|i\<less\>n> and
    <math|p\<nmid\>a<rsub|n>> we have <math|\<phi\><around*|(|f|)>\<sim\>X<rsup|n>>.

    Since <math|X\<in\>\<bbb-F\><rsub|p><around*|[|X|]>> is prime and
    <math|\<bbb-F\><rsub|p><around*|[|X|]>> is a UFD, it follows that
    <math|\<phi\><around*|(|g|)>\<sim\>X<rsup|i>> and
    <math|\<phi\><around*|(|h|)>\<sim\>X<rsup|n-i>>(by Proposition 3.14). If
    <math|i\<gtr\>0> then <math|\<phi\><around*|(|g|)>> has zero constant
    coefficient and so <math|p> divides the constant coefficient of <math|g>.
    <math|a<rsub|0>> is the product of the constant coefficients of <math|g>
    and <math|h> and since <math|p<rsup|2>\<nmid\>a<rsub|0>> we conclude that
    <math|p> does not divide the constant coefficient of <math|h> <em|i.e.>
    <math|i=n>. But then <math|deg g\<geqslant\>deg
    \<phi\><around*|(|g|)>=n>, and <math|n=deg f=deg g+deg h>, so <math|deg
    h=0>. Since <math|f> is primitive, <math|h> is then a unit and so
    <math|g\<sim\>f>.

    The case <math|i=0> is handled similarly and has <math|g\<sim\>1>
  </proof>

  <\example>
    For <math|n\<in\><math|\<bbb-N\><rsup|\<ast\>>>>, the polynomial
    <math|X<rsup|n>-2> is irreducible in <math|\<bbb-Z\>[X]> by Eisenstein's
    Criterion with the prime 2 since it is visibly primitive (with the lead
    coefficient being 1).
  </example>

  References

  [Ber14] D. Berlyne. Ideal theory in rings (Translation of \PIdealtheorie in
  Ringbereichen\Q by Emmy Noether). 2014, arXiv:1401.2577.

  [CNT19] C. J. Conidis, P. P. Nielsen, and V. Tombs. Transfinitely valued
  euclidean domains have arbitrary indecomposable order type. Communications
  in Algebra, 47(3):1105\U1113, 2019. doi:10.1080/00927872.2018.1501569.

  [Con] K. Conrad. Remarks about Euclidean domains. URL

  https://kconrad.math.uconn.edu/blurbs/ringtheory/euclideanrk.pdf.

  [Fuc58] L. Fuchs. Abelian groups. Publishing House of the Hungarian Academy
  of Sciences, Budapest, 1958.

  [Gra74] A. Grams. Atomic rings and the ascending chain condition for
  principal ideals. Proc. Cambridge Philos. Soc., 75:321\U329, 1974.
  doi:10.1017/s0305004100048532.

  [Kap70] I. Kaplansky. Commutative rings. Allyn and Bacon, Inc., Boston,
  Mass., 1970.

  [Kea98] M. E. Keating. A First Course in Module Theory. Imperial College
  Press, 1998. doi:https://doi.org/10.1142/p082.

  [Lam07] T. Y. Lam. Exercises in modules and rings. Problem Books in
  Mathematics. Springer, New York, 2007. doi:10.1007/978-0-387-48899-8.

  [Lan02] S. Lang. Algebra, volume 211 of Graduate Texts in Mathematics.
  Springer-Verlag, New York, third edition, 2002.
  doi:10.1007/978-1-4613-0041-0.

  [Noe21] E. Noether. Idealtheorie in Ringbereichen. Math. Ann.,
  83(1-2):24\U66, 1921. doi:10.1007/BF01464225.

  [Poo19] B. Poonen. Why all rings should have a 1. Math. Mag., 92(1):58\U62,
  2019. doi:10.1080/0025570X.2018.1538714.

  [She88] K. Shen. The historical development of the Chinese remainder
  theorem. J. Hangzhou Univ. Natur. Sci. Ed., 15(3):270\U282, 1988.

  [Sou20] K. Soundararajan. Bertrand's postulate and the existence of finite
  fields. 2020, arXiv:2007.01389.

  [Tol04] J. R. R. Tolkein. The Fellowship of the Ring. The Lord of the Rings
  Part I. HarperCollins e-books, 50th anniversary edition, 2004.
  <hlink|URL|https://s3.amazonaws.com/scschoolfiles/112/j-r-r-tolkien-lord-of-the-rings-01-the-fellowship-of-the-ring-retail-pdf.pdf><page-break>

  <section|Modules: an introduction>

  \;
</body>

<\initial>
  <\collection>
    <associate|font-base-size|11>
    <associate|info-flag|none>
    <associate|page-height|auto>
    <associate|page-medium|paper>
    <associate|page-screen-bot|15mm>
    <associate|page-screen-top|15mm>
    <associate|page-type|a4>
    <associate|page-width|auto>
  </collection>
</initial>

<\references>
  <\collection>
    <associate|auto-1|<tuple|1|1>>
    <associate|auto-10|<tuple|1.9|10>>
    <associate|auto-11|<tuple|2|12>>
    <associate|auto-12|<tuple|2.1|13>>
    <associate|auto-13|<tuple|2.2|15>>
    <associate|auto-14|<tuple|2.3|15>>
    <associate|auto-15|<tuple|2.4|16>>
    <associate|auto-16|<tuple|2.5|17>>
    <associate|auto-17|<tuple|2.6|17>>
    <associate|auto-18|<tuple|2.7|18>>
    <associate|auto-19|<tuple|3|19>>
    <associate|auto-2|<tuple|1.1|1>>
    <associate|auto-20|<tuple|3.1|20>>
    <associate|auto-21|<tuple|3.2|23>>
    <associate|auto-22|<tuple|3.3|24>>
    <associate|auto-23|<tuple|3.4|25>>
    <associate|auto-24|<tuple|4|28>>
    <associate|auto-3|<tuple|1.2|2>>
    <associate|auto-4|<tuple|1.3|3>>
    <associate|auto-5|<tuple|1.4|4>>
    <associate|auto-6|<tuple|1.5|5>>
    <associate|auto-7|<tuple|1.6|6>>
    <associate|auto-8|<tuple|1.7|6>>
    <associate|auto-9|<tuple|1.8|8>>
    <associate|footnote-1.1|<tuple|1.1|1>>
    <associate|footnote-1.2|<tuple|1.2|2>>
    <associate|footnote-2.1|<tuple|2.1|13>>
    <associate|footnr-1.1|<tuple|1.1|1>>
    <associate|footnr-1.2|<tuple|1.2|2>>
    <associate|footnr-2.1|<tuple|2.1|13>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|toc>
      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|1<space|2spc>Rings>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-1><vspace|0.5fn>

      <with|par-left|<quote|1tab>|1.1<space|2spc>Units and the trivial ring
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-2>>

      <with|par-left|<quote|1tab>|1.2<space|2spc>The integers and
      characteristic <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-3>>

      <with|par-left|<quote|1tab>|1.3<space|2spc>Isomorphisms and subrings
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-4>>

      <with|par-left|<quote|1tab>|1.4<space|2spc>Fields
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-5>>

      <with|par-left|<quote|1tab>|1.5<space|2spc>Zero divisors and integral
      domains <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-6>>

      <with|par-left|<quote|1tab>|1.6<space|2spc>Product of rings
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-7>>

      <with|par-left|<quote|1tab>|1.7<space|2spc>Prototypical rings
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-8>>

      <with|par-left|<quote|1tab>|1.8<space|2spc>Matrix rings
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-9>>

      <with|par-left|<quote|1tab>|1.9<space|2spc>Polynomial rings
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-10>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|2<space|2spc>Ideals
      and quotients> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-11><vspace|0.5fn>

      <with|par-left|<quote|1tab>|2.1<space|2spc>Quotient rings
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-12>>

      <with|par-left|<quote|1tab>|2.2<space|2spc>The Chinese Remainder
      Theorem <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-13>>

      <with|par-left|<quote|1tab>|2.3<space|2spc>The First Isomorphism
      Theorem and consequences <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-14>>

      <with|par-left|<quote|1tab>|2.4<space|2spc>Relationship between ideals
      in <with|mode|<quote|math>|R> and <with|mode|<quote|math>|R/I>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-15>>

      <with|par-left|<quote|1tab>|2.5<space|2spc>Proper, prime, and maximal
      ideals <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-16>>

      <with|par-left|<quote|1tab>|2.6<space|2spc>Discussion of fields of
      fractions and their characterisation
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-17>>

      <with|par-left|<quote|1tab>|2.7<space|2spc>Field extensions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-18>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|3<space|2spc>Divisibility>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-19><vspace|0.5fn>

      <with|par-left|<quote|1tab>|3.1<space|2spc>Irreducibles, primes, and
      uniqueness of factorisation <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-20>>

      <with|par-left|<quote|1tab>|3.2<space|2spc>Euclidean domains and
      division algorithms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-21>>

      <with|par-left|<quote|1tab>|3.3<space|2spc>The ACCP and unique
      factorisation domains <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-22>>

      <with|par-left|<quote|1tab>|3.4<space|2spc>Finding irreducibles
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-23>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|4<space|2spc>Modules:
      an introduction> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-24><vspace|0.5fn>
    </associate>
  </collection>
</auxiliary>