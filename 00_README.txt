

    The Proofs about Alpha-equivalences in Isabelle.

    (Created: 2016-01-07 +0900, Time-stamp: <2020-06-22T04:58:14Z>)


** Abstract

The word of "occurrence" in terms is useful to explain notions
intuitively, which frequently leads proofs into ambiguous and
inaccurate ones.  With theorem provers on the computer like Isabelle,
however, we can handle the proofs strictly and maybe complicatedly.
In the archive I show, I proved notions of the lambda calculus on the
computer especially about alpha-equivalence(s) handling with
occurrences.

The second merit was that though I was lacking confidence about
mathematics, I could affirm my proofs were correct because of theorem
provers.  However, I originally proved the proofs in Isabelle before
1998.  When I have proved originally, I certainly have comprehended
what I did.  Now, I almost don't recognize what I do, but I rewrite
the legacy proofs into the present style of the Isabelle2015.  Though,
I often consider proofs partly when rewriting leads to failure.  I
can't prove in the recommended style of Isar structured proof, but
prove in the style of "apply ... done" proofs with tactics and
tacticals.

The proofs about alpha-equivalence(s) of the lambda calculus include
the proof of correspondence between the definition of
alpha-equivalence using occurrences and that using inductive set, and
proofs about connection of the usual notation and de Bruijn notation.


** Contents

In the archive, we have *.thy files, which are the proofs.  I dedicate
the works to the Isabelle2015.  If you want to load all of the works
into the Isabelle2015, you open AllLambda.thy from jEdit or console
system.  (With jEdit, at first you must select Logics_ZF of logics of
Theories panel, and restart Isabelle2015, and open AllLambda.thy.)

Though the Isabelle2015 have many mechanisms of documentation, I don't
leave comments at all, because I write above that now I don't
recognize my work correctly.

In the "legacy" directory of the archive, I put the legacy proofs on
Isabelle before 1998 for reference.  It may be convenient if you must
prove the same lemmas in the future.  They are more readable than
those for the Isabelle2015.  The legacy proofs were the contents of my
master's thesis in Hokkaido University.

The tutorial advice bound variable should be rewritten by rewrite_tac,
but I can't obey the advice, because the number of bound variables is
many in complicated proof and the temporal names isn't changed from
the legacy proof for the most part.


** Homepage

I put the archive in a page of my blog which is written in Japanese.
The page is below:

  http://jrf.cocolog-nifty.com/software/2016/01/post.html

You can get the sources from GitHub:

  https://github.com/JRF-2018/isabelle_TheLambda


** Author

  JRF (http://jrf.cocolog-nifty.com)


** License

The author is a Japanese.

I intended this program to be public-domain, but you can treat
this program under the (new) BSD-License or under the Artistic
License, if it is convenient for you.

Within three months after the release of this program, I
especially admit responsibility of efforts for rational requests
of correction to this program.

I often have bouts of schizophrenia, but I believe that my
intention is legitimately fulfilled.


** P.S. (2020-06-22)

Now, I made the proofs compatible with Isabelle2020. The old proofs
for Isabelle2015 is moved into the directory of "legacy2015".


** 要約

項の中の「出現」という語は、概念を説明するのに便利だが、しばしば、証明
をあいまいで不正確なものにしがちである。しかし、それを Isabelle のよう
な定理証明システム上で行うなら話が違う。その証明は、たとえ複雑なものに
なったとしても、とても厳密なものにできる。このアーカイブでは、ラムダ計
算の特にα同値性に関して出現を用いて証明を行った。

この証明の第二の「売り」は、私が数学に関して素人で信用がないにもかかわ
らず、定理証明システムを使っているがゆえに正しいと肯定できるとう点にあっ
た。しかしながら、元々、この証明は Isabelle 上で 1998 年以前になされた
もので、そのころ証明したときには、何をやってるかを自分で理解できていた
が、今や、何をやっているかを理解しているとはいい難い。今回やったのは、
昔の証明を今の Isabelle2015 のスタイルに書き換えることだけである。もち
ろん、書き換えがうまくいかないことがあって、しばしば考え込むことがあっ
たが、証明の大枠の理解は抜け落ちている。書き換えるだけなので、推奨され
ている Isar structured proof のスタイルで証明することはできず、apply
... done タイプの tactics と tacticals を使う証明のスタイルの終始した。

ラムダ計算のα同値に関する証明では、出現を用いた定義と帰納的定義の一致
を証明したり、ラムダ計算の通常の表記法と de Bruijn 表記法の間の関係に
関する証明を行っている。


** アーカイブの内容

このアーカイブには、*.thy ファイルが含まれていて、それらが、証明になる。
Isabelle2015 用に専念して書かれているため、他のバージョン、例えば次のバー
ジョンでは動かないかもしれないほど依存性が高い。私の証明のすべてを
Isabelle2015 に読み込ませるには、jEdit かコンソールシステム上から
AllLambda.thy を読み込めばいい。(jEdit では、まず、Theories パネルの論
理を選ぶところで Logics_ZF を選び、Isabelle2015 を再起動した上で、
AllLambda.thy を読み込ませる必要がある。)

Isabelle2015 はドキュメント化のための様々な便宜を提供しているが、それ
らはまったく利用せず、コメントすら残していない。上にも書いたように現在
の私は証明を理解しているとは言い難いというのがその理由の一つである。

アーカイブの中の "legacy" ディレクトリには、1998年以前にやった証明を一
応含めておいた。もし、読者が私と同じ証明をすることになったら、
Isabelle2015 上の証明より、legacy な証明のほうが参照しやすいと思ったか
らだ。なお、legacy な証明は、私の北海道大学での修士論文(相当)の内容だっ
た。

チュートリアルでは、束縛変数名を証明内で参照するときには、rewrite_tac
を使って名前を与えよとアドバイスしているが、それにはしたがえなかった。
最初はしたがおうとしたが、束縛変数の数がとても多くなり、それでも、
legacy な証明とほとんどの場合、名前の使い方が変わっていないことから、
結局、ひよった。


** このアーカイブのホームページ

アーカイブは、私の(日本語の)ブログ内の一ページに置かれている。その URL
は以下の通り：

  http://jrf.cocolog-nifty.com/software/2016/01/post.html

もしくは以下の GitHub にある。

  https://github.com/JRF-2018/isabelle_TheLambda


** 著者

  JRF (http://jrf.cocolog-nifty.com)

** ライセンス

(上の英語版のライセンスを読んで下さい。)


** 追記 (2020-06-22)

Isabelle2020 に対応させた。Isabelle2015 用は、legacy2015 にある。



(This file was written in Japanese/UTF8.)
