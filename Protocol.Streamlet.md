# STREAMLET: Textbook Streamlined Blockchains

<pre class="Agda"><a id="56" class="Symbol">{-#</a> <a id="60" class="Keyword">OPTIONS</a> <a id="68" class="Pragma">--safe</a> <a id="75" class="Symbol">#-}</a>
<a id="79" class="Keyword">open</a> <a id="84" class="Keyword">import</a> <a id="91" href="Prelude.html" class="Module">Prelude</a>
<a id="99" class="Keyword">open</a> <a id="104" class="Keyword">import</a> <a id="111" href="Hash.html" class="Module">Hash</a>

<a id="117" class="Keyword">open</a> <a id="122" class="Keyword">import</a> <a id="129" href="Protocol.Streamlet.Assumptions.html" class="Module">Protocol.Streamlet.Assumptions</a>

<a id="161" class="Keyword">module</a> <a id="168" href="Protocol.Streamlet.html" class="Module">Protocol.Streamlet</a> <a id="187" class="Symbol">(</a><a id="188" href="Protocol.Streamlet.html#188" class="Bound">⋯</a> <a id="190" class="Symbol">:</a> <a id="192" href="Protocol.Streamlet.Assumptions.html#222" class="Record">Assumptions</a><a id="203" class="Symbol">)</a> <a id="205" class="Keyword">where</a>

<a id="212" class="Keyword">open</a> <a id="217" class="Keyword">import</a> <a id="224" href="Protocol.Streamlet.Base.html" class="Module">Protocol.Streamlet.Base</a> <a id="248" class="Keyword">public</a>
<a id="255" class="Keyword">open</a> <a id="260" class="Keyword">import</a> <a id="267" href="Protocol.Streamlet.Assumptions.html" class="Module">Protocol.Streamlet.Assumptions</a> <a id="298" class="Keyword">public</a>

<a id="306" class="Keyword">open</a> <a id="311" class="Keyword">import</a> <a id="318" href="Protocol.Streamlet.Block.html" class="Module">Protocol.Streamlet.Block</a> <a id="343" href="Protocol.Streamlet.html#188" class="Bound">⋯</a> <a id="345" class="Keyword">public</a>
<a id="352" class="Keyword">open</a> <a id="357" class="Keyword">import</a> <a id="364" href="Protocol.Streamlet.Message.html" class="Module">Protocol.Streamlet.Message</a> <a id="391" href="Protocol.Streamlet.html#188" class="Bound">⋯</a> <a id="393" class="Keyword">public</a>
<a id="400" class="Keyword">open</a> <a id="405" class="Keyword">import</a> <a id="412" href="Protocol.Streamlet.Local.Chain.html" class="Module">Protocol.Streamlet.Local.Chain</a> <a id="443" href="Protocol.Streamlet.html#188" class="Bound">⋯</a> <a id="445" class="Keyword">public</a>
<a id="452" class="Keyword">open</a> <a id="457" class="Keyword">import</a> <a id="464" href="Protocol.Streamlet.Local.State.html" class="Module">Protocol.Streamlet.Local.State</a> <a id="495" href="Protocol.Streamlet.html#188" class="Bound">⋯</a> <a id="497" class="Keyword">public</a>
<a id="504" class="Keyword">open</a> <a id="509" class="Keyword">import</a> <a id="516" href="Protocol.Streamlet.Local.Step.html" class="Module">Protocol.Streamlet.Local.Step</a> <a id="546" href="Protocol.Streamlet.html#188" class="Bound">⋯</a> <a id="548" class="Keyword">public</a>
<a id="555" class="Keyword">open</a> <a id="560" class="Keyword">import</a> <a id="567" href="Protocol.Streamlet.Global.State.html" class="Module">Protocol.Streamlet.Global.State</a> <a id="599" href="Protocol.Streamlet.html#188" class="Bound">⋯</a> <a id="601" class="Keyword">public</a>
<a id="608" class="Keyword">open</a> <a id="613" class="Keyword">import</a> <a id="620" href="Protocol.Streamlet.Global.Step.html" class="Module">Protocol.Streamlet.Global.Step</a> <a id="651" href="Protocol.Streamlet.html#188" class="Bound">⋯</a> <a id="653" class="Keyword">public</a>
<a id="660" class="Keyword">open</a> <a id="665" class="Keyword">import</a> <a id="672" href="Protocol.Streamlet.Global.Traces.html" class="Module">Protocol.Streamlet.Global.Traces</a> <a id="705" href="Protocol.Streamlet.html#188" class="Bound">⋯</a> <a id="707" class="Keyword">public</a>
</pre>