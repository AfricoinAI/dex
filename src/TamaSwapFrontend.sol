// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @title TamaSwap onchain frontend
/// @notice ERC-5219 HTML frontend for the Tama Uniswap V2 router and factory.
/// @dev Generated from html/tamaswap.html by script/build-tamaswap.mjs.
contract TamaSwapFrontend {
    string public constant NAME = "TamaSwap";
    string public constant VERSION = "0.1";

    address public immutable factory;
    address public immutable router;
    address public immutable PAYLOAD;

    struct KeyValue { string key; string value; }

    constructor(address factory_, address router_) payable {
        require(factory_ != address(0), "factory zero");
        require(router_ != address(0), "router zero");
        factory = factory_;
        router = router_;
        PAYLOAD = _deployData(bytes(string.concat(
            "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"
            )));
    }

    function _deployData(bytes memory payload) private returns (address d) {
        require(payload.length <= 0xFFFF, "payload too big");
        bytes memory initcode = bytes.concat(hex"61", bytes2(uint16(payload.length)), hex"80600a5f395ff3", payload);
        assembly ("memory-safe") { d := create(0, add(initcode, 0x20), mload(initcode)) }
        require(d != address(0), "deploy failed");
    }

    function html() external view returns (string memory) {
        return _html();
    }

    function request(string[] memory resource, KeyValue[] memory)
        external
        view
        returns (uint16 statusCode, string memory body, KeyValue[] memory headers)
    {
        if (!_isIndexResource(resource)) {
            statusCode = 404;
            body = "Not found";
            headers = new KeyValue[](1);
            headers[0] = KeyValue("Content-Type", "text/plain; charset=utf-8");
            return (statusCode, body, headers);
        }
        statusCode = 200;
        body = _html();
        headers = new KeyValue[](3);
        headers[0] = KeyValue("Content-Type", "text/html; charset=utf-8");
        headers[1] = KeyValue("Cache-Control", "public, max-age=31536000, immutable");
        headers[2] = KeyValue("Content-Security-Policy", "default-src 'none'; script-src 'unsafe-inline'; style-src 'unsafe-inline'; img-src https: data: http://localhost:* http://127.0.0.1:*; connect-src https: http://localhost:* http://127.0.0.1:*; base-uri 'none'; form-action 'none'");
    }

    function resolveMode() external pure returns (bytes32) {
        return "5219";
    }

    function _isIndexResource(string[] memory resource) private pure returns (bool) {
        if (resource.length == 0) return true;
        if (resource.length == 1) {
            bytes32 value = keccak256(bytes(resource[0]));
            return value == keccak256(bytes("")) || value == keccak256(bytes("/")) || value == keccak256(bytes("index.html"));
        }
        return false;
    }

    function _html() private view returns (string memory) {
        return string.concat(
            "<!doctype html><script>(async()=>{const F=\"",
            _addr(factory),
            "\",R=\"",
            _addr(router),
            "\",B=\"",
            _data(PAYLOAD),
            "\";try{let u=Uint8Array.from(atob(B),c=>c.charCodeAt()),h=await new Response(new Blob([u]).stream().pipeThrough(new DecompressionStream(\"gzip\"))).text();h=h.replace(\"__\"+\"FACTORY__\",F).replace(\"__\"+\"ROUTER__\",R);document.open().write(h);document.close()}catch{document.body.textContent=\"TamaSwap load failed\"}})()</script>"
        );
    }

    function _data(address target) private view returns (string memory s) {
        assembly ("memory-safe") {
            let size := extcodesize(target)
            s := mload(0x40)
            mstore(s, size)
            let ptr := add(s, 0x20)
            extcodecopy(target, ptr, 0, size)
            let padded := and(add(size, 0x1f), not(0x1f))
            mstore(0x40, add(add(s, 0x20), padded))
        }
    }

    function _addr(address account) private pure returns (string memory) {
        bytes20 value = bytes20(account);
        bytes16 symbols = "0123456789abcdef";
        bytes memory out = new bytes(42);
        out[0] = "0";
        out[1] = "x";
        for (uint256 i = 0; i < 20; i++) {
            out[2 + i * 2] = symbols[uint8(value[i] >> 4)];
            out[3 + i * 2] = symbols[uint8(value[i] & 0x0f)];
        }
        return string(out);
    }
}

/* ===== tamaswap.html source, 37477 bytes minified, 11286 bytes gzip before base64 =====

<!doctype html>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>TamaSwap</title>
<link rel="icon" href="data:,">
<style>
*{box-sizing:border-box}button,input{font:inherit}body{margin:0;min-height:100vh;background:radial-gradient(circle at 50% -10%,#ffe4f3 0,#f7f8fb 34%,#eef2f6 100%);color:#111827;font:15px/1.35 ui-sans-serif,system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif}.top{max-width:1180px;margin:0 auto;padding:18px 18px 0;display:flex;justify-content:space-between;align-items:center}.brand{display:flex;align-items:center;gap:10px;font-weight:800;font-size:20px}.mark{width:34px;height:34px;border-radius:11px;background:#ff4da6;color:white;display:grid;place-items:center;font-weight:900}.nav{display:flex;gap:6px;background:#fff8;border:1px solid #fff;border-radius:18px;padding:4px}.nav button{border:0;border-radius:14px;background:transparent;padding:9px 15px;color:#6b7280;font-weight:700;cursor:pointer}.nav button.on{background:white;color:#111827;box-shadow:0 6px 18px #11182712}.wallet{border:0;background:#ff4da6;color:white;border-radius:18px;padding:10px 16px;font-weight:800;cursor:pointer}.wallet.ok{background:white;color:#111827;box-shadow:0 4px 16px #11182712}.shell{max-width:480px;margin:58px auto 36px;padding:0 14px}.card{background:#fff;border:1px solid #ffffffcc;border-radius:28px;box-shadow:0 24px 70px #1f293726;padding:10px;overflow:hidden}.head{display:flex;justify-content:space-between;align-items:center;padding:10px 12px 6px}.title{font-size:17px;font-weight:800}.muted{color:#6b7280}.gear{border:0;border-radius:12px;background:#f3f4f6;color:#6b7280;padding:8px 11px;font-size:13px;font-weight:800;cursor:pointer}.box{background:#f5f6fa;border:1px solid #edf0f5;border-radius:22px;padding:16px;margin:4px 0;min-width:0}.box:focus-within{border-color:#ff9dcb}.lbl{display:flex;justify-content:space-between;gap:10px;color:#6b7280;font-size:13px;margin-bottom:8px}.bal{white-space:nowrap;overflow:hidden;text-overflow:ellipsis}.bal:not(:empty){cursor:pointer;color:#4b5563}.bal:not(:empty):hover{color:#ff2f94}.amount{display:flex;gap:10px;align-items:center;min-width:0}.amount input{min-width:0;flex:1;border:0;background:transparent;outline:0;color:#111827;font-size:34px;font-weight:650;letter-spacing:0}.amount input::placeholder{color:#c6cbd3}.tok{border:0;border-radius:999px;background:white;color:#111827;box-shadow:0 3px 13px #11182714;padding:8px 10px;min-width:116px;max-width:150px;font-weight:850;display:flex;align-items:center;justify-content:center;gap:7px;cursor:pointer;overflow:hidden}.tok span:last-child{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}.tok.empty{background:#ff4da6;color:white}.logo{flex:0 0 auto;width:24px;height:24px;border-radius:50%;background:linear-gradient(135deg,#ff4da6,#7c3aed);display:grid;place-items:center;color:white;font-size:11px;font-weight:900;overflow:hidden}.logo img{width:100%;height:100%;object-fit:cover}.flip{display:grid;place-items:center;margin:-10px 0;position:relative;z-index:2}.flip button{width:36px;height:36px;border:4px solid white;border-radius:13px;background:#f5f6fa;color:#6b7280;font-size:18px;cursor:pointer}.review{background:#fafafa;border-radius:18px;padding:12px;margin:8px 0;display:grid;gap:9px}.review div{display:flex;justify-content:space-between;gap:12px}.review a,.status a{color:#ff2f94;font-weight:800;text-decoration:none}.review a:hover,.status a:hover{text-decoration:underline}.cta{width:100%;border:0;border-radius:20px;background:#ff4da6;color:white;padding:16px;font-weight:900;font-size:17px;cursor:pointer}.cta:disabled{background:#f3c9df;color:#a98095;cursor:not-allowed}.soft{width:100%;border:0;border-radius:16px;background:#f3f4f6;color:#111827;padding:13px;font-weight:800;cursor:pointer}.row{display:grid;grid-template-columns:minmax(0,1fr) minmax(0,1fr);gap:8px}.status{min-height:22px;padding:10px 12px 2px;color:#6b7280;font-size:13px;overflow-wrap:anywhere}.status.err{color:#dc2626}.hide{display:none}.poolMode{display:flex;gap:6px;padding:4px;background:#f5f6fa;border-radius:18px;margin:4px 0 10px}.poolMode button{flex:1;border:0;border-radius:14px;background:transparent;padding:9px;font-weight:800;color:#6b7280;cursor:pointer}.poolMode button.on{background:white;color:#111827;box-shadow:0 4px 14px #1118270f}.modal{position:fixed;inset:0;background:#11182780;display:none;align-items:center;justify-content:center;padding:16px;z-index:10}.modal.on{display:flex}.sheet{width:min(430px,100%);max-height:82vh;background:white;border-radius:26px;box-shadow:0 24px 90px #0008;overflow:hidden;display:flex;flex-direction:column}.sheetHead{padding:18px;display:flex;justify-content:space-between;align-items:center}.x{border:0;background:#f3f4f6;border-radius:12px;width:34px;height:34px;cursor:pointer}.search{margin:0 18px 12px;border:1px solid #e5e7eb;border-radius:18px;padding:13px 14px;outline:0}.list{overflow:auto;padding:0 8px 10px}.item{display:flex;align-items:center;gap:12px;width:100%;border:0;background:white;border-radius:16px;padding:10px;cursor:pointer;text-align:left}.item:hover{background:#f6f7fb}.sym{font-weight:850}.addr{font-size:12px;color:#9ca3af}.manage{border-top:1px solid #edf0f5;padding:12px 18px 16px;display:grid;gap:8px}.url{border:1px solid #e5e7eb;border-radius:14px;padding:11px;outline:0}.tiny{font-size:12px;color:#6b7280}.pill{display:inline-flex;align-items:center;gap:6px;background:#f3f4f6;border-radius:999px;padding:5px 9px}.mono{font-family:ui-monospace,SFMono-Regular,Menlo,monospace}.space{height:8px}.setrow{display:flex;justify-content:space-between;gap:12px;align-items:center;padding:0 18px 14px}.setrow input{width:92px;border:1px solid #e5e7eb;border-radius:14px;padding:10px;outline:0;text-align:right}@media(max-width:620px){.top{gap:10px;flex-wrap:wrap}.nav{order:3;width:100%;justify-content:center}.shell{margin-top:28px}.amount input{font-size:30px}.row{grid-template-columns:1fr}.tok{min-width:108px}}
</style>
<div class=top>
  <div class=brand><div class=mark>T</div><span>TamaSwap</span></div>
  <div class=nav><button id=tabSwap class=on>Swap</button><button id=tabPool>Pool</button></div>
  <button id=connect class=wallet>Connect</button>
</div>
<main class=shell>
  <section id=swapView class=card>
    <div class=head><div class=title>Swap</div><button id=settings class=gear>Settings</button></div>
    <div class=box>
      <div class=lbl><span>You pay</span><span id=balIn class=bal></span></div>
      <div class=amount><input id=swapAmt inputmode=decimal placeholder=0><button id=pickIn class="tok empty">Select token</button></div>
    </div>
    <div class=flip><button id=flip>v</button></div>
    <div class=box>
      <div class=lbl><span>You receive</span><span id=balOut class=bal></span></div>
      <div class=amount><input id=swapOutAmt inputmode=decimal placeholder=0><button id=pickOut class="tok empty">Select token</button></div>
    </div>
    <div id=swapReview class="review hide">
      <div><span id=swapLimitLabel class=muted>Minimum received</span><b id=minOut>-</b></div>
      <div><span class=muted>Price status</span><span id=priceState>Price unavailable until tokens are selected</span></div>
    </div>
    <button id=swapCta class=cta disabled>Enter an amount</button>
    <div id=stat class=status></div>
  </section>
  <section id=poolView class="card hide">
    <div class=head><div class=title>Pool</div><div><span id=chain class="pill tiny">Not connected</span> <button id=poolSettings class=gear>Settings</button></div></div>
    <div class=poolMode><button data-pool=add class=on>Add</button><button data-pool=remove>Remove</button></div>
    <div id=addPool>
      <div class=box><div class=lbl><span>Token A</span><span id=lpBalA class=bal></span></div><div class=amount><input id=lpAmtA inputmode=decimal placeholder=0><button id=pickLpA class="tok empty">Select token</button></div></div>
      <div class=box><div class=lbl><span>Token B</span><span id=lpBalB class=bal></span></div><div class=amount><input id=lpAmtB inputmode=decimal placeholder=0><button id=pickLpB class="tok empty">Select token</button></div></div>
      <div id=lpReview class="review hide"><div><span class=muted>Pool</span><span id=lpPoolState>-</span></div><div><span class=muted>Price</span><span id=lpPrice>-</span></div><div><span class=muted>Minimum deposit</span><span id=lpMin>-</span></div></div>
      <button id=lpCta class=cta disabled>Enter amounts</button>
    </div>
    <div id=removePool class=hide>
      <div class=box><div class=lbl><span>Token A</span></div><button id=pickBurnA class="tok empty">Select token</button></div>
      <div class=box><div class=lbl><span>Token B</span></div><button id=pickBurnB class="tok empty">Select token</button></div>
      <div class=box><div class=lbl><span>LP amount</span><span id=lpBal class=bal></span></div><div class=amount><input id=burnLiq inputmode=decimal placeholder=0></div></div>
      <div id=burnReview class="review hide"><div><span class=muted>Pair</span><span id=pairInfo>-</span></div><div id=burnOutRow class=hide><span class=muted>You receive</span><span id=burnOut>-</span></div><div id=burnMinRow class=hide><span class=muted>Minimum received</span><span id=burnMin>-</span></div></div>
      <button id=burnCta class=cta disabled>Select pool</button>
    </div>
    <div id=poolStat class=status></div>
  </section>
</main>
<div id=modal class=modal>
  <div class=sheet>
    <div class=sheetHead><b>Select token</b><button id=closeModal class=x>x</button></div>
    <input id=search class=search placeholder="Search name or paste address" autocomplete=off spellcheck=false>
    <div id=tokens class=list></div>
    <div class=manage>
      <b>Manage token lists</b>
      <input id=listUrl class=url value="https://tokens.uniswap.org">
      <button id=loadList class=soft>Import token list</button>
      <div id=listStat class=tiny>Loads Uniswap Token Lists JSON for the connected chain.</div>
    </div>
  </div>
</div>
<div id=walletModal class=modal>
  <div class=sheet>
    <div class=sheetHead><b>Connect wallet</b><button id=closeWallet class=x>x</button></div>
    <div id=wallets class=list></div>
    <div class=manage><div id=walletStat class=tiny>Looking for installed wallets.</div></div>
  </div>
</div>
<div id=settingsModal class=modal>
  <div class=sheet>
    <div class=sheetHead><b>Settings</b><button id=closeSettings class=x>x</button></div>
    <div class=setrow><span>Max slippage</span><label><input id=slip inputmode=decimal value="0.5"> %</label></div>
    <div class=setrow><span>Infinite approvals</span><label><input id=maxApproval type=checkbox></label></div>
    <div class=manage><div class=tiny>Exact approvals are the default. Enable infinite approvals only when you want one reusable approval for this router.</div></div>
  </div>
</div>
<script>
const FACTORY="__FACTORY__",ROUTER="__ROUTER__",DEFAULT_LIST="https://tokens.uniswap.org";
let E=null,AC=null,CID=1,WETH_ADDR="",activePick="",TOK=[],MAP=new Map(),SEL={},PX=new Map(),PAIR=null,WALLETS=[],lastLpEdit="",lastSwapEdit="in",lastAct={},allowCache=new Map(),BURN=[0n,0n],QUOTE=[0n,0n],quoteSeq=0,lpSeq=0,burnSeq=0;
const CHAIN={1:{e:"etherscan.io",l:"ethereum"},11155111:{e:"sepolia.etherscan.io",l:""},56:{e:"bscscan.com",l:"bsc"},97:{e:"testnet.bscscan.com",l:""},8453:{e:"basescan.org",l:"base"},84532:{e:"sepolia.basescan.org",l:""},42161:{e:"arbiscan.io",l:"arbitrum"},421614:{e:"sepolia.arbiscan.io",l:""},137:{e:"polygonscan.com",l:"polygon"},80002:{e:"amoy.polygonscan.com",l:""},4326:{e:"mega.etherscan.io",l:"megaeth"},6343:{e:"megaeth-testnet-v2.blockscout.com",l:""},9745:{e:"plasmascan.to",l:"plasma"},9746:{e:"testnet.plasmascan.to",l:""},43114:{e:"snowscan.xyz",l:"avax"},43113:{e:"testnet.snowscan.xyz",l:""},143:{e:"monadvision.com",l:"monad"},10143:{e:"testnet.monadexplorer.com",l:""},10:{e:"optimistic.etherscan.io",l:"optimism"},11155420:{e:"sepolia-optimism.etherscan.io",l:""},25:{e:"explorer.cronos.org",l:"cronos"},338:{e:"explorer.cronos.org/testnet",l:""},57073:{e:"explorer.inkonchain.com",l:"ink"},763373:{e:"explorer-sepolia.inkonchain.com",l:""},173:{e:"scan.eniac.network",l:"eni"},174:{e:"scan-testnet.eniac.network",l:""},5000:{e:"mantlescan.xyz",l:"mantle"},5003:{e:"explorer.sepolia.mantle.xyz",l:""},3073:{e:"explorer.movementlabs.xyz",l:"movement"},30732:{e:"explorer.testnet.imola.movementlabs.xyz",l:""},31337:{e:"http://127.0.0.1:5100",l:""},1337:{e:"http://127.0.0.1:5100",l:""}};
const $=id=>document.getElementById(id),isA=x=>/^0x[0-9a-fA-F]{40}$/.test(x||""),low=x=>(x||"").toLowerCase(),sh=x=>x?x.slice(0,6)+"..."+x.slice(-4):"",p32=v=>BigInt(v).toString(16).padStart(64,"0"),ea=a=>low(a).slice(2).padStart(64,"0"),dl=()=>Math.floor(Date.now()/1000)+1200;
function clean(s,n=64){return String(s||"").replace(/[\u0000-\u001f\u007f-\u009f\u200b-\u200f\u202a-\u202e\u2066-\u2069]/g,"").trim().slice(0,n)}
function isLocalUrl(u){return ["localhost","127.0.0.1","::1"].includes(u.hostname)||u.hostname.endsWith(".localhost")}
function safeUrl(v,{data=false,local=true}={}){v=String(v||"").trim();if(!v)return "";try{if(data&&/^data:image\//i.test(v))return v;if(!/^https?:\/\//i.test(v))return "";let u=new URL(v);if(u.protocol==="https:"||(local&&isLocalUrl(u)&&(u.protocol==="http:"||u.protocol==="https:")))return u.href.replace(/\/$/,"")}catch(e){}return ""}
function safeJson(s,f){try{return JSON.parse(s)}catch(e){return f}}
function hexData(h,words=1){if(!/^0x[0-9a-fA-F]*$/.test(h||"")||h.length<2+64*words)throw Error("Bad ABI response");return h.slice(2)}
function word(h,i=0){return hexData(h,i+1).slice(i*64,i*64+64)}
function uintAt(h,i=0){return BigInt("0x"+word(h,i))}
function addrAt(h,i=0){let w=word(h,i);return low("0x"+w.slice(24))}
const rpc=(m,p)=>E.request({method:m,params:p}),cd=(s,a="")=>s+a,raw=async(to,data)=>await rpc("eth_call",[{to,data},"latest"]),tx=async(to,data,value=0n)=>{let q={from:AC,to,data};if(BigInt(value)>0n)q.value="0x"+BigInt(value).toString(16);return await rpc("eth_sendTransaction",[q])};
function status(x,b=false,pool=false){const e=pool?poolStat:stat;e.textContent=x||"";e.title=x||"";e.className=b?"status err":"status"}
function explorer(kind,v){let h=localStorage["tamaExplorer:"+CID]||CHAIN[CID]?.e;if(!h)return "";h=safeUrl(/^https?:\/\//.test(h)?h:"https://"+h);return h?`${h}/${kind}/${v}`:""}
function link(el,kind,v,label=sh(v)){let u=explorer(kind,v);el.textContent="";if(u){let a=document.createElement("a");a.href=u;a.target="_blank";a.rel="noopener noreferrer";a.textContent=label;el.append(a)}else el.textContent=label}
function done(h,pool=false){const e=pool?poolStat:stat;status("Transaction submitted",false,pool);let u=explorer("tx",h);e.append(" ");if(u){let a=document.createElement("a");a.href=u;a.target="_blank";a.rel="noopener noreferrer";a.textContent="View transaction";e.append(a)}else e.append(sh(h))}
function show(e,on){e.classList.toggle("hide",!on)}
function parseAmt(s,d){s=(s||"").trim();if(!s)return 0n;if(!/^\d*(\.\d*)?$/.test(s)||s===".")throw Error("Invalid amount");let [i,f=""]=s.split(".");f=(f+"0".repeat(d)).slice(0,d);return BigInt(i||0)*10n**BigInt(d)+BigInt(f||0)}
function fmtAmt(n,d){n=BigInt(n||0);let s=n.toString().padStart(d+1,"0"),i=s.slice(0,-d)||"0",f=s.slice(-d).replace(/0+$/,"");return f?i+"."+f.slice(0,6):i}
function fmtFull(n,d){n=BigInt(n||0);let s=n.toString().padStart(d+1,"0"),i=s.slice(0,-d)||"0",f=s.slice(-d).replace(/0+$/,"");return f?i+"."+f:i}
function slipBps(){let raw=(slip.value||"0.5").trim();if(!/^\d+(\.\d+)?$/.test(raw))throw Error("Invalid slippage");let v=Number(raw);if(!Number.isFinite(v)||v<=0||v>50)throw Error("Invalid slippage");return BigInt(Math.round(v*100))}
function minWithSlip(n){return BigInt(n||0)*(10000n-slipBps())/10000n}
function maxWithSlip(n){return BigInt(n||0)*(10000n+slipBps())/10000n}
function approvalAmount(n){return maxApproval.checked?2n**256n-1n:BigInt(n||0)}
function money(v){return v==null?"":v>=1?"$"+v.toLocaleString(undefined,{maximumFractionDigits:2}):"$"+v.toPrecision(3)}
function btn(b,t){b.className="tok";b.textContent="";let l=document.createElement("span");l.className="logo";if(t?.logoURI){let im=document.createElement("img");im.src=t.logoURI;l.append(im)}else l.textContent=(t?.symbol||"?").slice(0,2);let s=document.createElement("span");s.textContent=t?.symbol||"Select token";b.append(l,s);if(!t)b.classList.add("empty")}
function selected(k){return SEL[k]}function need(){if(!AC)throw Error("Connect wallet first")}
function isNative(t){return !!t?.native}
function nativeToken(){return WETH_ADDR?{address:low(WETH_ADDR),symbol:"ETH",name:"Ether",decimals:18,logoURI:"",native:true}:null}
function sameAsset(a,b){return a&&b&&low(a.address)===low(b.address)}
function wrapPair(a,b){return sameAsset(a,b)&&isNative(a)!==isNative(b)}
function setSel(k,t){SEL[k]=t;btn($(k),t);allowCache.clear();updateAll()}
function priceFallback(){priceState.textContent="Price unavailable"}
function walletName(w,i){let p=w.provider,n=w.info?.name;if(n)return n;if(p?.isMetaMask)return "MetaMask";if(p?.isCoinbaseWallet)return "Coinbase Wallet";if(p?.isRabby)return "Rabby";return "Wallet "+(i+1)}
function addWallet(p,i={}){if(!p||WALLETS.some(w=>w.provider===p))return;WALLETS.push({provider:p,info:i});p.on?.("chainChanged",()=>location.reload());p.on?.("accountsChanged",()=>location.reload());renderWallets()}
function renderWallets(){wallets.textContent="";WALLETS.forEach((w,i)=>{let b=document.createElement("button");b.className="item";let l=document.createElement("span");l.className="logo";if(w.info?.icon){let im=document.createElement("img");im.src=w.info.icon;l.append(im)}else l.textContent=walletName(w,i).slice(0,2);let d=document.createElement("div"),s=document.createElement("div"),a=document.createElement("div");s.className="sym";s.textContent=walletName(w,i);a.className="addr";a.textContent=w.info?.rdns||"Injected wallet";d.append(s,a);b.append(l,d);b.onclick=()=>connectWallet(w.provider).catch(e=>status(e.message,true));wallets.append(b)});walletStat.textContent=WALLETS.length?`${WALLETS.length} wallet${WALLETS.length===1?"":"s"} detected`:"No wallet detected"}
function detectWallets(){window.addEventListener("eip6963:announceProvider",e=>addWallet(e.detail?.provider,e.detail?.info||{}));window.dispatchEvent(new Event("eip6963:requestProvider"));let eth=window.ethereum;if(eth?.providers)eth.providers.forEach((p,i)=>addWallet(p,{name:p.name||walletName({provider:p},i)}));else if(eth)addWallet(eth,{name:"Browser wallet"});setTimeout(renderWallets,100)}
async function connectWallet(p){if(p)E=p;if(!E){if(WALLETS.length===1)return connectWallet(WALLETS[0].provider);throw Error("No wallet detected")}let a=await rpc("eth_requestAccounts",[]);AC=a[0];CID=Number(await rpc("eth_chainId",[]));connect.textContent=sh(AC);connect.className="wallet ok";chain.textContent="Chain "+CID;walletModal.classList.remove("on");await loadLists();updateAll()}
function openWallets(){if(WALLETS.length===1)connectWallet(WALLETS[0].provider).catch(e=>status(e.message,true));else{renderWallets();walletModal.classList.add("on")}}
connect.onclick=openWallets;closeWallet.onclick=()=>walletModal.classList.remove("on");walletModal.onclick=e=>{if(e.target===walletModal)walletModal.classList.remove("on")};settings.onclick=poolSettings.onclick=()=>settingsModal.classList.add("on");closeSettings.onclick=()=>settingsModal.classList.remove("on");settingsModal.onclick=e=>{if(e.target===settingsModal)settingsModal.classList.remove("on")};slip.oninput=updateAll;
detectWallets();setTimeout(()=>{if(WALLETS[0]){E=WALLETS[0].provider;rpc("eth_accounts",[]).then(async a=>{CID=Number(await rpc("eth_chainId",[]));if(a[0]){AC=a[0];connect.textContent=sh(AC);connect.className="wallet ok";chain.textContent="Chain "+CID}await loadLists()}).catch(()=>loadLists())}else loadLists()},150);
async function loadWETH(){if(!E)return;try{WETH_ADDR=addrAt(await raw(ROUTER,"0xad5c4648"))}catch(e){WETH_ADDR="";listStat.textContent="Router WETH lookup failed. Native ETH routes are hidden."}}
function savedLists(){let urls=safeJson(localStorage.tamaLists||"null",null);return Array.isArray(urls)?urls.filter(u=>safeUrl(u)).slice(0,5):[DEFAULT_LIST]}
async function loadLists(){await loadWETH();listStat.textContent=WETH_ADDR?"Loading token list...":"Router WETH lookup failed. Loading token list without native ETH.";let all=[];for(let u of savedLists()){u=safeUrl(u);if(!u)continue;try{let j=await (await fetch(u)).json();if(!Array.isArray(j.tokens))throw Error("bad list");all.push(...j.tokens.filter(t=>t&&t.chainId===CID&&isA(t.address)&&Number.isInteger(Number(t.decimals))).map(t=>({address:low(t.address),symbol:clean(t.symbol||"???",16)||"???",name:clean(t.name||t.symbol||"Token",48)||"Token",decimals:Number(t.decimals),logoURI:safeUrl(t.logoURI||"",{data:true})})))}catch(e){listStat.textContent="Token list unavailable. Paste a token address to import manually."}}let m=new Map();all.forEach(t=>m.set(t.address,t));if(WETH_ADDR&&!m.has(WETH_ADDR))m.set(WETH_ADDR,{address:WETH_ADDR,symbol:"WETH",name:"Wrapped Ether",decimals:18,logoURI:""});let nt=nativeToken();TOK=[...(nt?[nt]:[]),...[...m.values()].sort((a,b)=>a.symbol.localeCompare(b.symbol))];MAP=m;listStat.textContent=TOK.length?`${TOK.length} tokens loaded for chain ${CID}`:"No listed tokens for this chain. Paste an address.";renderTokens()}
loadList.onclick=async()=>{let u=safeUrl(listUrl.value.trim());if(!u){listStat.textContent="Use an HTTPS token list URL or localhost development URL.";return}let urls=savedLists();if(!urls.includes(u))urls.unshift(u);localStorage.tamaLists=JSON.stringify(urls.slice(0,5));await loadLists()};
function openPick(k){activePick=k;modal.classList.add("on");search.value="";renderTokens();search.focus()}
closeModal.onclick=()=>modal.classList.remove("on");modal.onclick=e=>{if(e.target===modal)modal.classList.remove("on")};search.oninput=renderTokens;
["pickIn","pickOut","pickLpA","pickLpB","pickBurnA","pickBurnB"].forEach(id=>$(id).onclick=()=>openPick(id));
async function tokenMeta(a){let t=MAP.get(low(a));if(t)return t;need();let d=18,sym="TOKEN",name="Token";try{d=Number(uintAt(await raw(a,"0x313ce567")))}catch(e){}try{sym=clean(decStr(await raw(a,"0x95d89b41"))||sym,16)}catch(e){}try{name=clean(decStr(await raw(a,"0x06fdde03"))||name,48)}catch(e){}t={address:low(a),symbol:sym||"TOKEN",name:name||"Token",decimals:d,logoURI:"",unverified:true};MAP.set(t.address,t);TOK.unshift(t);return t}
function decStr(h){let raw=hexData(h),w=word(h);if(raw.length===64)return clean(hexToText(w),48);let o=Number(BigInt("0x"+w))*2,l=Number(BigInt("0x"+raw.slice(o,o+64)))*2;if(raw.length<o+64+l)throw Error("Bad string ABI");return clean(hexToText(raw.slice(o+64,o+64+l)),48)}
function hexToText(h){let s="";for(let i=0;i<h.length;i+=2){let c=parseInt(h.slice(i,i+2),16);if(c)s+=String.fromCharCode(c)}return s.trim()}
function renderTokens(){tokens.textContent="";let q=low(search.value.trim()),arr=TOK.filter(t=>!q||low(t.symbol).includes(q)||low(t.name).includes(q)||low(t.address).includes(q)).slice(0,80);if(isA(q)&&!MAP.has(q))arr=[{address:q,symbol:"Import",name:"Import token by address",decimals:18,unverified:true},...arr];for(let t of arr){let b=document.createElement("button");b.className="item";let l=document.createElement("span");l.className="logo";l.textContent=(t.symbol||"?").slice(0,2);let d=document.createElement("div"),s=document.createElement("div"),a=document.createElement("div");s.className="sym";s.textContent=t.symbol;a.className="addr";a.append((t.unverified?"Unverified token - ":t.name+" - "));let u=explorer("address",t.address);if(u&&!t.native){let x=document.createElement("a");x.href=u;x.target="_blank";x.rel="noopener noreferrer";x.textContent=sh(t.address);x.onclick=e=>e.stopPropagation();a.append(x)}else a.append(t.native?"Native ETH":sh(t.address));d.append(s,a);b.append(l,d);b.onclick=async()=>{let x=t.native?t:await tokenMeta(t.address);setSel(activePick,x);modal.classList.remove("on")};tokens.append(b)}}
async function balance(t){if(!AC||!t)return null;if(isNative(t)){try{return BigInt(await rpc("eth_getBalance",[AC,"latest"]))}catch(e){return null}}try{return uintAt(await raw(t.address,cd("0x70a08231",ea(AC))))}catch(e){return null}}
async function allowance(t,spender=ROUTER){if(!AC||!t||isNative(t))return 2n**256n-1n;let k=t.address+":"+spender,c=allowCache.get(k);if(c!=null)return c;try{let v=uintAt(await raw(t.address,cd("0xdd62ed3e",ea(AC)+ea(spender))));allowCache.set(k,v);return v}catch(e){return 0n}}
async function totalSupply(a){try{return uintAt(await raw(a,"0x18160ddd"))}catch(e){return 0n}}
async function price(t){if(!t)return null;let slug=CHAIN[CID]?.l;if(!slug)return null;let k=slug+":"+t.address,c=PX.get(k);if(c&&Date.now()-c.ts<60000)return c.p;try{let j=await (await fetch("https://coins.llama.fi/prices/current/"+k)).json(),p=j?.coins?.[k]?.price;if(typeof p==="number"&&p>0){PX.set(k,{p,ts:Date.now()});return p}}catch(e){}PX.set(k,{p:null,ts:Date.now()});return null}
async function updateUsd(inp,t,out){let p=await price(t),v=parseFloat(inp.value||"0");if(out)out.textContent=p&&v?money(v*p):"";if(!QUOTE[0]||!QUOTE[1])priceState.textContent=p?"DeFiLlama pricing":"Price unavailable"}
function pairFor(a,b){return raw(FACTORY,cd("0xe6a43905",ea(a)+ea(b))).then(r=>addrAt(r))}
async function reserves(a,b){let p=await pairFor(a,b);if(BigInt(p)===0n)return [p,0n,0n];let r=await raw(p,"0x0902f1ac"),x=uintAt(r,0),y=uintAt(r,1),t0=addrAt(await raw(p,"0x0dfe1681"));return [p,...(low(a)===t0?[x,y]:[y,x])]}
async function impact(seq,a,b,input,output,exactOut){let [,ra,rb]=await reserves(a.address,b.address);if(seq!==quoteSeq||ra===0n||rb===0n||input===0n||output===0n)return;let ppm;if(exactOut){let ideal=input?output*ra*1000000n/rb:0n;ppm=input>ideal?(input-ideal)*1000000n/input:0n}else{let ideal=input*rb/ra;ppm=ideal>output?(ideal-output)*1000000n/ideal:0n}if(seq===quoteSeq)priceState.textContent="Price impact "+(Number(ppm)/10000).toFixed(2)+"%"}
async function setBal(el,t,label="Balance",inp=null,edit=""){let b=await balance(t);el.onclick=null;el.title="";el.dataset.value="";if(b==null||!t){el.textContent="";return null}el.textContent=`${label}: ${fmtAmt(b,t.decimals)} ${t.symbol}`;el.dataset.value=fmtFull(b,t.decimals);if(inp){el.title="Use full balance";el.onclick=()=>{inp.value=el.dataset.value;if(edit==="A"||edit==="B")lastLpEdit=edit;if(edit==="in"||edit==="out")lastSwapEdit=edit;updateAll()}}return b}
async function quote(){
let seq=++quoteSeq,a=selected("pickIn"),b=selected("pickOut"),amt,want,exactOut=lastSwapEdit==="out";
try{amt=parseAmt(swapAmt.value,a?.decimals||18);want=parseAmt(swapOutAmt.value,b?.decimals||18);slipBps()}catch(e){if(seq!==quoteSeq)return;swapCta.textContent=e.message;swapCta.disabled=true;show(swapReview,false);return}
QUOTE=[0n,0n];await setBal(balIn,a,"Balance",swapAmt,"in");await setBal(balOut,b);if(seq!==quoteSeq)return;lastAct.swap="none";swapCta.disabled=true;show(swapReview,false);
if(!a||!b){swapCta.textContent="Select tokens";if(!exactOut)swapOutAmt.value="";return}
priceFallback();
if(sameAsset(a,b)&&!wrapPair(a,b)){swapCta.textContent="Select different tokens";if(!exactOut)swapOutAmt.value="";return}
if((exactOut?want:amt)===0n){swapCta.textContent="Enter an amount";if(!exactOut)swapOutAmt.value="";updateUsd(swapAmt,a,null);updateUsd(swapOutAmt,b,null);return}
show(swapReview,true);swapLimitLabel.textContent=exactOut?"Maximum sold":"Minimum received";
try{
let r,al,bal;
if(wrapPair(a,b)){
let q=exactOut?want:amt;QUOTE=[q,q];if(exactOut)swapAmt.value=fmtAmt(q,a.decimals);else swapOutAmt.value=fmtAmt(q,b.decimals);minOut.textContent=fmtAmt(q,b.decimals)+" "+(exactOut?a.symbol:b.symbol);
bal=await balance(a);if(seq!==quoteSeq)return;if(bal!=null&&bal<q){swapCta.textContent="Insufficient "+a.symbol;return}
if(isNative(a)){swapCta.textContent="Wrap";lastAct.swap="wrap"}else{al=await allowance(a);if(seq!==quoteSeq)return;if(al<q){swapCta.textContent="Approve "+a.symbol;lastAct.swap="approve"}else{swapCta.textContent="Unwrap";lastAct.swap="unwrap"}}
swapCta.disabled=false;return
}
if(exactOut){
r=await raw(ROUTER,cd("0x1f00ca74",p32(want)+p32(64)+p32(2)+ea(a.address)+ea(b.address)));amt=uintAt(r,2);if(seq!==quoteSeq)return;QUOTE=[amt,want];let max=maxWithSlip(amt);swapAmt.value=fmtAmt(amt,a.decimals);minOut.textContent=fmtAmt(max,a.decimals)+" "+a.symbol;
bal=await balance(a);if(seq!==quoteSeq)return;if(bal!=null&&bal<(isNative(a)?max:amt)){swapCta.textContent="Insufficient "+a.symbol;return}
al=await allowance(a);if(seq!==quoteSeq)return;if(al<max){swapCta.textContent="Approve "+a.symbol;lastAct.swap="approve"}else{swapCta.textContent=isNative(a)?"Swap - unused ETH is refunded":"Swap";lastAct.swap="out"}
}else{
r=await raw(ROUTER,cd("0xd06ca61f",p32(amt)+p32(64)+p32(2)+ea(a.address)+ea(b.address)));let out=uintAt(r,3),min=minWithSlip(out);if(seq!==quoteSeq)return;QUOTE=[amt,out];swapOutAmt.value=fmtAmt(out,b.decimals);minOut.textContent=fmtAmt(min,b.decimals)+" "+b.symbol;
bal=await balance(a);if(seq!==quoteSeq)return;if(bal!=null&&bal<amt){swapCta.textContent="Insufficient "+a.symbol;return}
al=await allowance(a);if(seq!==quoteSeq)return;if(al<amt){swapCta.textContent="Approve "+a.symbol;lastAct.swap="approve"}else{swapCta.textContent="Swap";lastAct.swap="in"}
}
swapCta.disabled=false
}catch(e){if(seq!==quoteSeq)return;if(!exactOut)swapOutAmt.value="";minOut.textContent="-";swapCta.textContent="No liquidity";status("No route or insufficient liquidity",true)}
updateUsd(swapAmt,a,null);updateUsd(swapOutAmt,b,null)
if(QUOTE[0]&&QUOTE[1]&&!wrapPair(a,b))impact(seq,a,b,QUOTE[0],QUOTE[1],exactOut).catch(()=>{})
}
async function updateLp(){let seq=++lpSeq,a=selected("pickLpA"),b=selected("pickLpB"),aa,bb;try{aa=parseAmt(lpAmtA.value,a?.decimals||18);bb=parseAmt(lpAmtB.value,b?.decimals||18);slipBps()}catch(e){lpCta.textContent=e.message;lpCta.disabled=true;show(lpReview,false);return}await setBal(lpBalA,a,"Balance",lpAmtA,"A");await setBal(lpBalB,b,"Balance",lpAmtB,"B");if(seq!==lpSeq)return;lastAct.lp="none";lpCta.disabled=true;show(lpReview,false);if(!a||!b){lpCta.textContent="Select tokens";return}if(sameAsset(a,b)){lpCta.textContent="Select different tokens";return}let [p,ra,rb]=await reserves(a.address,b.address);if(seq!==lpSeq)return;let exists=BigInt(p)!==0n;if(exists&&ra>0n&&rb>0n){lpPoolState.textContent="Add to existing pool";if(lastLpEdit==="A"&&aa>0n){bb=aa*rb/ra;lpAmtB.value=fmtAmt(bb,b.decimals)}if(lastLpEdit==="B"&&bb>0n){aa=bb*ra/rb;lpAmtA.value=fmtAmt(aa,a.decimals)}lpPrice.textContent=aa||bb?`1 ${a.symbol} = ${fmtAmt(rb*10n**BigInt(a.decimals)/ra,b.decimals)} ${b.symbol}`:"-"}else{lpPoolState.textContent=aa&&bb?"New pool will be created. Gas will be higher.":"New pool available";lpPrice.textContent=aa&&bb?`Initial price: 1 ${a.symbol} = ${fmtAmt(bb*10n**BigInt(a.decimals)/aa,b.decimals)} ${b.symbol}`:"-"}lpMin.textContent=aa&&bb?`${fmtAmt(minWithSlip(aa),a.decimals)} ${a.symbol} / ${fmtAmt(minWithSlip(bb),b.decimals)} ${b.symbol}`:"-";show(lpReview,!!(aa||bb));if(!aa||!bb){lpCta.textContent="Enter amounts";return}let ba=await balance(a),bbal=await balance(b);if(seq!==lpSeq)return;if(ba!=null&&ba<aa){lpCta.textContent="Insufficient "+a.symbol;return}if(bbal!=null&&bbal<bb){lpCta.textContent="Insufficient "+b.symbol;return}let ala=await allowance(a),alb=await allowance(b);if(seq!==lpSeq)return;if(ala<aa||alb<bb){lpCta.textContent="Approve tokens";lastAct.lp="approve"}else{lpCta.textContent=exists?"Add liquidity":"Create pool and add liquidity";lastAct.lp="add"}lpCta.disabled=false}
async function checkPair(){let seq=++burnSeq,a=selected("pickBurnA"),b=selected("pickBurnB");lastAct.burn="none";BURN=[0n,0n];burnCta.disabled=true;show(burnReview,false);show(burnOutRow,false);show(burnMinRow,false);await setBal(lpBal,null);if(seq!==burnSeq)return;if(!a||!b){burnCta.textContent="Select pool";return}if(sameAsset(a,b)){burnCta.textContent="Select different tokens";return}let [p,ra,rb]=await reserves(a.address,b.address);if(seq!==burnSeq)return;PAIR=p;show(burnReview,true);if(BigInt(p)===0n){pairInfo.textContent="No pair found";burnCta.textContent="No pool";return}link(pairInfo,"address",p);let pairTok={address:p,decimals:18,symbol:"LP"};let bal=await setBal(lpBal,pairTok,"Balance",burnLiq),liq;try{liq=parseAmt(burnLiq.value,18);slipBps()}catch(e){burnCta.textContent=e.message;return}if(seq!==burnSeq)return;if(liq===0n){burnCta.textContent="Enter LP amount";return}let supply=await totalSupply(p),outA=supply?liq*ra/supply:0n,outB=supply?liq*rb/supply:0n;if(seq!==burnSeq)return;BURN=[outA,outB];burnOut.textContent=`${fmtAmt(outA,a.decimals)} ${a.symbol} / ${fmtAmt(outB,b.decimals)} ${b.symbol}`;burnMin.textContent=`${fmtAmt(minWithSlip(outA),a.decimals)} ${a.symbol} / ${fmtAmt(minWithSlip(outB),b.decimals)} ${b.symbol}`;show(burnOutRow,true);show(burnMinRow,true);if(bal!=null&&bal<liq){burnCta.textContent="Insufficient LP";return}let al=await allowance(pairTok);if(seq!==burnSeq)return;if(al<liq){burnCta.textContent="Approve LP";lastAct.burn="approve"}else{burnCta.textContent="Remove liquidity";lastAct.burn="remove"}burnCta.disabled=false}
function updateAll(){quote().catch(()=>{});updateLp().catch(()=>{});checkPair().catch(()=>{})}
swapAmt.oninput=()=>{lastSwapEdit="in";updateAll()};swapOutAmt.oninput=()=>{lastSwapEdit="out";updateAll()};lpAmtA.oninput=()=>{lastLpEdit="A";updateAll()};lpAmtB.oninput=()=>{lastLpEdit="B";updateAll()};burnLiq.oninput=updateAll;flip.onclick=()=>{let a=selected("pickIn"),b=selected("pickOut"),x=swapAmt.value,y=swapOutAmt.value;SEL.pickIn=b;SEL.pickOut=a;btn(pickIn,b);btn(pickOut,a);allowCache.clear();swapAmt.value=y;swapOutAmt.value=x;lastSwapEdit=lastSwapEdit==="out"?"in":"out";updateAll()};
tabSwap.onclick=()=>{tabSwap.className="on";tabPool.className="";swapView.classList.remove("hide");poolView.classList.add("hide")};tabPool.onclick=()=>{tabPool.className="on";tabSwap.className="";poolView.classList.remove("hide");swapView.classList.add("hide")};
document.querySelectorAll("[data-pool]").forEach(b=>b.onclick=()=>{document.querySelectorAll("[data-pool]").forEach(x=>x.classList.remove("on"));b.classList.add("on");addPool.classList.toggle("hide",b.dataset.pool!=="add");removePool.classList.toggle("hide",b.dataset.pool!=="remove");poolStat.textContent="";updateAll()});
function approveData(spender,amt){return cd("0x095ea7b3",ea(spender)+p32(amt))}
async function approveToken(t,amount,spender=ROUTER){need();if(!t)throw Error("Select token first");if(isNative(t))throw Error("Native ETH does not need approval");let h=await tx(t.address,approveData(spender,approvalAmount(amount)));allowCache.clear();return h}
swapCta.onclick=async()=>{try{let a=selected("pickIn"),b=selected("pickOut"),path=p32(2)+ea(a.address)+ea(b.address);if(lastAct.swap==="approve"){await quote();done(await approveToken(a,lastSwapEdit==="out"?maxWithSlip(QUOTE[0]):QUOTE[0]));return updateAll()}if(lastAct.swap==="wrap"){await quote();if(lastAct.swap!=="wrap")return;done(await tx(ROUTER,cd("0x406ee863",ea(AC)),QUOTE[0]));return updateAll()}if(lastAct.swap==="unwrap"){await quote();if(lastAct.swap!=="unwrap")return;done(await tx(ROUTER,cd("0x2e59d848",p32(QUOTE[0])+ea(AC))));return updateAll()}if(lastAct.swap==="in"){await quote();if(lastAct.swap!=="in")return;let d;if(isNative(a)){d=cd("0x7ff36ab5",p32(minWithSlip(QUOTE[1]))+p32(128)+ea(AC)+p32(dl())+path);done(await tx(ROUTER,d,QUOTE[0]))}else if(isNative(b)){d=cd("0x18cbafe5",p32(QUOTE[0])+p32(minWithSlip(QUOTE[1]))+p32(160)+ea(AC)+p32(dl())+path);done(await tx(ROUTER,d))}else{d=cd("0x38ed1739",p32(QUOTE[0])+p32(minWithSlip(QUOTE[1]))+p32(160)+ea(AC)+p32(dl())+path);done(await tx(ROUTER,d))}return updateAll()}if(lastAct.swap==="out"){await quote();if(lastAct.swap!=="out")return;let d,max=maxWithSlip(QUOTE[0]);if(isNative(a)){d=cd("0xfb3bdb41",p32(QUOTE[1])+p32(128)+ea(AC)+p32(dl())+path);done(await tx(ROUTER,d,max))}else if(isNative(b)){d=cd("0x4a25d94a",p32(QUOTE[1])+p32(max)+p32(160)+ea(AC)+p32(dl())+path);done(await tx(ROUTER,d))}else{d=cd("0x8803dbee",p32(QUOTE[1])+p32(max)+p32(160)+ea(AC)+p32(dl())+path);done(await tx(ROUTER,d))}return updateAll()}}catch(e){status(e.message,true)}};
lpCta.onclick=async()=>{try{let a=selected("pickLpA"),b=selected("pickLpB"),aa=parseAmt(lpAmtA.value,a?.decimals||18),bb=parseAmt(lpAmtB.value,b?.decimals||18);if(lastAct.lp==="approve"){if(!isNative(a)&&await allowance(a)<aa)done(await approveToken(a,aa),true);if(!isNative(b)&&await allowance(b)<bb)done(await approveToken(b,bb),true);return updateAll()}if(lastAct.lp==="add"){let d;if(isNative(a)||isNative(b)){let t=isNative(a)?b:a,ta=isNative(a)?bb:aa,eth=isNative(a)?aa:bb;d=cd("0xf305d719",ea(t.address)+p32(ta)+p32(minWithSlip(ta))+p32(minWithSlip(eth))+ea(AC)+p32(dl()));done(await tx(ROUTER,d,eth),true)}else{d=cd("0xe8e33700",ea(a.address)+ea(b.address)+p32(aa)+p32(bb)+p32(minWithSlip(aa))+p32(minWithSlip(bb))+ea(AC)+p32(dl()));done(await tx(ROUTER,d),true)}return updateAll()}}catch(e){status(e.message,true,true)}};
burnCta.onclick=async()=>{try{let a=selected("pickBurnA"),b=selected("pickBurnB");await checkPair();let liq=parseAmt(burnLiq.value,18),pairTok={address:PAIR,decimals:18,symbol:"LP"};if(lastAct.burn==="approve"){done(await approveToken(pairTok,liq),true);return updateAll()}if(lastAct.burn==="remove"){let d;if(isNative(a)||isNative(b)){let t=isNative(a)?b:a,mt=isNative(a)?BURN[1]:BURN[0],me=isNative(a)?BURN[0]:BURN[1];d=cd("0x02751cec",ea(t.address)+p32(liq)+p32(minWithSlip(mt))+p32(minWithSlip(me))+ea(AC)+p32(dl()))}else d=cd("0xbaa2abde",ea(a.address)+ea(b.address)+p32(liq)+p32(minWithSlip(BURN[0]))+p32(minWithSlip(BURN[1]))+ea(AC)+p32(dl()));done(await tx(ROUTER,d),true);return updateAll()}}catch(e){status(e.message,true,true)}};
</script>

===== end tamaswap.html source ===== */
