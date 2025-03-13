# Index
<pre class="Agda"><a id="17" class="Comment">-- {-# OPTIONS --safe #-}</a>

<a id="44" class="Comment">-- ** prerequisites</a>
<a id="64" class="Keyword">open</a> <a id="69" class="Keyword">import</a> <a id="76" href="Prelude.html" class="Module">Prelude</a>
<a id="84" class="Keyword">open</a> <a id="89" class="Keyword">import</a> <a id="96" href="Hash.html" class="Module">Hash</a>

<a id="102" class="Comment">-- ** the Streamlet protocol</a>
<a id="131" class="Keyword">open</a> <a id="136" class="Keyword">import</a> <a id="143" href="Protocol.Streamlet.html" class="Module">Protocol.Streamlet</a>

<a id="163" class="Comment">-- ** decision procedures</a>
<a id="189" class="Keyword">open</a> <a id="194" class="Keyword">import</a> <a id="201" href="Protocol.Streamlet.Decidability.html" class="Module">Protocol.Streamlet.Decidability</a>

<a id="234" class="Comment">-- ** mechanized proof of consistency</a>
<a id="272" class="Keyword">open</a> <a id="277" class="Keyword">import</a> <a id="284" href="Protocol.Streamlet.Properties.html" class="Module">Protocol.Streamlet.Properties</a>

<a id="315" class="Comment">-- ** example trace</a>
<a id="335" class="Keyword">open</a> <a id="340" class="Keyword">import</a> <a id="347" href="DummyHashing.html" class="Module">DummyHashing</a> <a id="360" class="Comment">{- unsafe -}</a>
<a id="373" class="Keyword">open</a> <a id="378" class="Keyword">import</a> <a id="385" href="Protocol.Streamlet.Test.Core.html" class="Module">Protocol.Streamlet.Test.Core</a>
<a id="414" class="Keyword">open</a> <a id="419" class="Keyword">import</a> <a id="426" href="Protocol.Streamlet.Test.ExampleTrace.html" class="Module">Protocol.Streamlet.Test.ExampleTrace</a>

<a id="464" class="Comment">-- ** trace verifier</a>
<a id="485" class="Keyword">open</a> <a id="490" class="Keyword">import</a> <a id="497" href="Protocol.Streamlet.TraceVerifier.html" class="Module">Protocol.Streamlet.TraceVerifier</a>
<a id="530" class="Keyword">open</a> <a id="535" class="Keyword">import</a> <a id="542" href="Protocol.Streamlet.Test.TraceVerifier.html" class="Module">Protocol.Streamlet.Test.TraceVerifier</a>

<a id="581" class="Comment">-- ** variants on trace verification</a>
<a id="618" class="Keyword">open</a> <a id="623" class="Keyword">import</a> <a id="630" href="Protocol.Streamlet.TraceVerifier.Intrinsic.html" class="Module">Protocol.Streamlet.TraceVerifier.Intrinsic</a>
<a id="673" class="Keyword">open</a> <a id="678" class="Keyword">import</a> <a id="685" href="Protocol.Streamlet.TraceVerifier.Reverse.html" class="Module">Protocol.Streamlet.TraceVerifier.Reverse</a>

<a id="727" class="Comment">-- ** other tests</a>
<a id="745" class="Keyword">open</a> <a id="750" class="Keyword">import</a> <a id="757" href="Protocol.Streamlet.Test.Block.html" class="Module">Protocol.Streamlet.Test.Block</a>
<a id="787" class="Keyword">open</a> <a id="792" class="Keyword">import</a> <a id="799" href="Protocol.Streamlet.Test.Chain.html" class="Module">Protocol.Streamlet.Test.Chain</a>
<a id="829" class="Keyword">open</a> <a id="834" class="Keyword">import</a> <a id="841" href="Protocol.Streamlet.Test.LocalState.html" class="Module">Protocol.Streamlet.Test.LocalState</a>
<a id="876" class="Keyword">open</a> <a id="881" class="Keyword">import</a> <a id="888" href="Protocol.Streamlet.Test.LocalState2.html" class="Module">Protocol.Streamlet.Test.LocalState2</a>
<a id="924" class="Keyword">open</a> <a id="929" class="Keyword">import</a> <a id="936" href="Protocol.Streamlet.StepVerifier.html" class="Module">Protocol.Streamlet.StepVerifier</a>
<a id="968" class="Keyword">open</a> <a id="973" class="Keyword">import</a> <a id="980" href="Protocol.Streamlet.Test.StepVerifier.html" class="Module">Protocol.Streamlet.Test.StepVerifier</a>
</pre>