(this.webpackJsonpinfura_experiments=this.webpackJsonpinfura_experiments||[]).push([[0],{73:function(e,t,n){},75:function(e,t,n){},78:function(e,t){},93:function(e,t,n){"use strict";n.r(t);var a=n(16),i=n.n(a),s=n(62),p=n.n(s),r=(n(73),n(3)),u=n.n(r),y=n(45),o=n(18),d=[{inputs:[],stateMutability:"nonpayable",type:"constructor"},{anonymous:!1,inputs:[{indexed:!0,internalType:"address",name:"owner",type:"address"},{indexed:!0,internalType:"address",name:"spender",type:"address"},{indexed:!1,internalType:"uint256",name:"value",type:"uint256"}],name:"Approval",type:"event"},{anonymous:!1,inputs:[{indexed:!0,internalType:"address",name:"sender",type:"address"},{indexed:!1,internalType:"uint192",name:"",type:"uint192"},{indexed:!0,internalType:"address",name:"to",type:"address"}],name:"Burn",type:"event"},{anonymous:!1,inputs:[{indexed:!0,internalType:"address",name:"sender",type:"address"},{indexed:!1,internalType:"uint192",name:"",type:"uint192"}],name:"Mint",type:"event"},{anonymous:!1,inputs:[{indexed:!0,internalType:"address",name:"",type:"address"},{indexed:!1,internalType:"uint192",name:"",type:"uint192"},{indexed:!1,internalType:"uint192",name:"",type:"uint192"},{indexed:!0,internalType:"address",name:"",type:"address"}],name:"Swap",type:"event"},{anonymous:!1,inputs:[{indexed:!1,internalType:"uint256",name:"",type:"uint256"}],name:"Sync",type:"event"},{anonymous:!1,inputs:[{indexed:!0,internalType:"address",name:"from",type:"address"},{indexed:!0,internalType:"address",name:"to",type:"address"},{indexed:!1,internalType:"uint256",name:"value",type:"uint256"}],name:"Transfer",type:"event"},{inputs:[],name:"DOMAIN_SEPARATOR",outputs:[{internalType:"bytes32",name:"",type:"bytes32"}],stateMutability:"view",type:"function"},{inputs:[],name:"PERMIT_TYPEHASH",outputs:[{internalType:"bytes32",name:"",type:"bytes32"}],stateMutability:"view",type:"function"},{inputs:[{internalType:"address",name:"",type:"address"},{internalType:"address",name:"",type:"address"}],name:"allowance",outputs:[{internalType:"uint256",name:"",type:"uint256"}],stateMutability:"view",type:"function"},{inputs:[{internalType:"address",name:"spender",type:"address"},{internalType:"uint256",name:"value",type:"uint256"}],name:"approve",outputs:[{internalType:"bool",name:"",type:"bool"}],stateMutability:"nonpayable",type:"function"},{inputs:[{internalType:"address",name:"",type:"address"}],name:"balanceOf",outputs:[{internalType:"uint256",name:"",type:"uint256"}],stateMutability:"view",type:"function"},{inputs:[],name:"decimals",outputs:[{internalType:"uint8",name:"",type:"uint8"}],stateMutability:"view",type:"function"},{inputs:[],name:"factory",outputs:[{internalType:"address",name:"",type:"address"}],stateMutability:"view",type:"function"},{inputs:[],name:"name",outputs:[{internalType:"string",name:"",type:"string"}],stateMutability:"view",type:"function"},{inputs:[{internalType:"address",name:"",type:"address"}],name:"nonces",outputs:[{internalType:"uint256",name:"",type:"uint256"}],stateMutability:"view",type:"function"},{inputs:[],name:"patron",outputs:[{internalType:"address",name:"",type:"address"}],stateMutability:"view",type:"function"},{inputs:[{internalType:"address",name:"owner",type:"address"},{internalType:"address",name:"spender",type:"address"},{internalType:"uint256",name:"value",type:"uint256"},{internalType:"uint256",name:"deadline",type:"uint256"},{internalType:"uint8",name:"v",type:"uint8"},{internalType:"bytes32",name:"r",type:"bytes32"},{internalType:"bytes32",name:"s",type:"bytes32"}],name:"permit",outputs:[],stateMutability:"nonpayable",type:"function"},{inputs:[],name:"priceCumulative",outputs:[{internalType:"uint256",name:"",type:"uint256"}],stateMutability:"view",type:"function"},{inputs:[],name:"symbol",outputs:[{internalType:"string",name:"",type:"string"}],stateMutability:"view",type:"function"},{inputs:[],name:"token0",outputs:[{internalType:"address",name:"",type:"address"}],stateMutability:"view",type:"function"},{inputs:[],name:"token1",outputs:[{internalType:"address",name:"",type:"address"}],stateMutability:"view",type:"function"},{inputs:[],name:"totalSupply",outputs:[{internalType:"uint256",name:"",type:"uint256"}],stateMutability:"view",type:"function"},{inputs:[{internalType:"address",name:"to",type:"address"},{internalType:"uint256",name:"value",type:"uint256"}],name:"transfer",outputs:[{internalType:"bool",name:"",type:"bool"}],stateMutability:"nonpayable",type:"function"},{inputs:[{internalType:"address",name:"from",type:"address"},{internalType:"address",name:"to",type:"address"},{internalType:"uint256",name:"value",type:"uint256"}],name:"transferFrom",outputs:[{internalType:"bool",name:"",type:"bool"}],stateMutability:"nonpayable",type:"function"},{inputs:[{internalType:"address",name:"_token0",type:"address"},{internalType:"address",name:"_token1",type:"address"},{internalType:"uint224",name:"circle",type:"uint224"}],name:"initialize",outputs:[],stateMutability:"nonpayable",type:"function"},{inputs:[{internalType:"uint224",name:"_circleData",type:"uint224"}],name:"ICO",outputs:[],stateMutability:"nonpayable",type:"function"},{inputs:[],name:"getReserves",outputs:[{internalType:"uint224",name:"_reserve",type:"uint224"},{internalType:"uint224",name:"_circleData",type:"uint224"}],stateMutability:"view",type:"function"},{inputs:[{internalType:"address",name:"to",type:"address"}],name:"mint",outputs:[{internalType:"uint256",name:"liquidity",type:"uint256"}],stateMutability:"nonpayable",type:"function"},{inputs:[{internalType:"address",name:"to",type:"address"}],name:"burn",outputs:[{internalType:"uint192",name:"amount",type:"uint192"}],stateMutability:"nonpayable",type:"function"},{inputs:[{internalType:"uint256",name:"amountOut",type:"uint256"},{internalType:"address",name:"to",type:"address"},{internalType:"bytes",name:"data",type:"bytes"}],name:"swap",outputs:[],stateMutability:"nonpayable",type:"function"},{inputs:[{internalType:"address",name:"to",type:"address"}],name:"skim",outputs:[],stateMutability:"nonpayable",type:"function"},{inputs:[],name:"sync",outputs:[],stateMutability:"nonpayable",type:"function"}],l=[{inputs:[],stateMutability:"nonpayable",type:"constructor"},{anonymous:!1,inputs:[{indexed:!0,internalType:"address",name:"owner",type:"address"},{indexed:!0,internalType:"address",name:"spender",type:"address"},{indexed:!1,internalType:"uint256",name:"value",type:"uint256"}],name:"Approval",type:"event"},{anonymous:!1,inputs:[{indexed:!0,internalType:"address",name:"from",type:"address"},{indexed:!0,internalType:"address",name:"to",type:"address"},{indexed:!1,internalType:"uint256",name:"value",type:"uint256"}],name:"Transfer",type:"event"},{inputs:[],name:"DOMAIN_SEPARATOR",outputs:[{internalType:"bytes32",name:"",type:"bytes32"}],stateMutability:"view",type:"function"},{inputs:[],name:"PERMIT_TYPEHASH",outputs:[{internalType:"bytes32",name:"",type:"bytes32"}],stateMutability:"view",type:"function"},{inputs:[{internalType:"address",name:"",type:"address"},{internalType:"address",name:"",type:"address"}],name:"allowance",outputs:[{internalType:"uint256",name:"",type:"uint256"}],stateMutability:"view",type:"function"},{inputs:[{internalType:"address",name:"spender",type:"address"},{internalType:"uint256",name:"value",type:"uint256"}],name:"approve",outputs:[{internalType:"bool",name:"",type:"bool"}],stateMutability:"nonpayable",type:"function"},{inputs:[{internalType:"address",name:"",type:"address"}],name:"balanceOf",outputs:[{internalType:"uint256",name:"",type:"uint256"}],stateMutability:"view",type:"function"},{inputs:[],name:"decimals",outputs:[{internalType:"uint8",name:"",type:"uint8"}],stateMutability:"view",type:"function"},{inputs:[{internalType:"string",name:"_name",type:"string"},{internalType:"string",name:"_symbol",type:"string"}],name:"initialize",outputs:[],stateMutability:"nonpayable",type:"function"},{inputs:[],name:"name",outputs:[{internalType:"string",name:"",type:"string"}],stateMutability:"view",type:"function"},{inputs:[{internalType:"address",name:"",type:"address"}],name:"nonces",outputs:[{internalType:"uint256",name:"",type:"uint256"}],stateMutability:"view",type:"function"},{inputs:[{internalType:"address",name:"owner",type:"address"},{internalType:"address",name:"spender",type:"address"},{internalType:"uint256",name:"value",type:"uint256"},{internalType:"uint256",name:"deadline",type:"uint256"},{internalType:"uint8",name:"v",type:"uint8"},{internalType:"bytes32",name:"r",type:"bytes32"},{internalType:"bytes32",name:"s",type:"bytes32"}],name:"permit",outputs:[],stateMutability:"nonpayable",type:"function"},{inputs:[],name:"symbol",outputs:[{internalType:"string",name:"",type:"string"}],stateMutability:"view",type:"function"},{inputs:[],name:"totalSupply",outputs:[{internalType:"uint256",name:"",type:"uint256"}],stateMutability:"view",type:"function"},{inputs:[{internalType:"address",name:"to",type:"address"},{internalType:"uint256",name:"value",type:"uint256"}],name:"transfer",outputs:[{internalType:"bool",name:"",type:"bool"}],stateMutability:"nonpayable",type:"function"},{inputs:[{internalType:"address",name:"from",type:"address"},{internalType:"address",name:"to",type:"address"},{internalType:"uint256",name:"value",type:"uint256"}],name:"transferFrom",outputs:[{internalType:"bool",name:"",type:"bool"}],stateMutability:"nonpayable",type:"function"}],m=n(50),c=n(15),b=(n(75),n(35)),T=n(10),f=new m.a.providers.Web3Provider(window.ethereum).getSigner(),j=new b.a("0xe03163cF98465662AB9447180da05e3390d700F8",[{inputs:[{internalType:"address payable",name:"_owner",type:"address"}],stateMutability:"nonpayable",type:"constructor"},{anonymous:!1,inputs:[{indexed:!0,internalType:"string",name:"name",type:"string"},{indexed:!0,internalType:"string",name:"symbol",type:"string"},{indexed:!1,internalType:"address",name:"pairAddress",type:"address"}],name:"erc20Created",type:"event"},{inputs:[{internalType:"string",name:"_name",type:"string"},{internalType:"string",name:"_symbol",type:"string"}],name:"createERC20",outputs:[{internalType:"address",name:"erc20Address",type:"address"}],stateMutability:"nonpayable",type:"function"},{inputs:[],name:"owner",outputs:[{internalType:"address payable",name:"",type:"address"}],stateMutability:"view",type:"function"}],f);var v=function(){var e=Object(a.useState)("_"),t=Object(o.a)(e,2),n=t[0],i=t[1],s=Object(a.useState)("_"),p=Object(o.a)(s,2),r=p[0],v=p[1],x=Object(a.useState)("0x..."),O=Object(o.a)(x,2),w=O[0],g=O[1],M=Object(a.useState)("0x..."),S=Object(o.a)(M,2),h=S[0],_=S[1],C=Object(a.useState)(0),k=Object(o.a)(C,2),A=k[0],R=k[1],E=Object(a.useState)("0x1ceE98B938F0AF112592353F0353AFEdE50d8eEA"),N=Object(o.a)(E,2),D=N[0],F=N[1],P=Object(a.useState)("_"),I=Object(o.a)(P,2),B=I[0],H=I[1],z=Object(a.useState)("_"),J=Object(o.a)(z,2),L=J[0],Y=J[1],q=Object(a.useState)("_"),U=Object(o.a)(q,2),W=U[0],G=U[1],K=Object(a.useState)("_"),Q=Object(o.a)(K,2),V=Q[0],X=Q[1],Z=Object(a.useState)("_"),$=Object(o.a)(Z,2),ee=$[0],te=$[1],ne=Object(a.useState)("_"),ae=Object(o.a)(ne,2),ie=ae[0],se=ae[1],pe=Object(a.useState)("_"),re=Object(o.a)(pe,2),ue=re[0],ye=re[1],oe=Object(a.useState)("_"),de=Object(o.a)(oe,2),le=de[0],me=de[1],ce=Object(a.useState)("_"),be=Object(o.a)(ce,2),Te=be[0],fe=be[1],je=Object(a.useState)("_"),ve=Object(o.a)(je,2),xe=ve[0],Oe=ve[1],we=Object(a.useState)("_"),ge=Object(o.a)(we,2),Me=ge[0],Se=ge[1],he=function(){var e=Object(y.a)(u.a.mark((function e(t){var n,a,i,s,p,r,y,l,b,T,j,v,x,O,w,g,M,S,h;return u.a.wrap((function(e){for(;;)switch(e.prev=e.next){case 0:return t.preventDefault(),n=c.a.from(2),a=new m.a.Contract(D,d,f),e.next=5,a.getReserves();case 5:return i=e.sent,s=Object(o.a)(i,2),p=s[0],r=s[1],y=c.a.from(r.toString()),l=c.a.from(p.toString()),b=l.div(n.pow(c.a.from(128))),T=l.div(n.pow(c.a.from(32))).mod(n.pow(c.a.from(96))),j=y.div(n.pow(c.a.from(216))),v=y.div(n.pow(c.a.from(160))).mod(n.pow(c.a.from(56))),x=y.div(n.pow(c.a.from(104))).mod(n.pow(c.a.from(56))),O=y.div(n.pow(c.a.from(88))).mod(n.pow(c.a.from(16))),w=y.div(n.pow(c.a.from(72))).mod(n.pow(c.a.from(16))),g=y.div(n.pow(c.a.from(56))).mod(n.pow(c.a.from(16))),M=y.mod(n.pow(c.a.from(56))),H(b.toString()),Y(T.toString()),G(j.toString()),X(v.toString()),te(x.toString()),se(O.toString()),ye(w.toString()),me(g.toString()),fe(M.toString()),e.next=31,a.token0();case 31:return S=e.sent,e.next=34,a.token1();case 34:h=e.sent,Oe(S.toString()),Se(h.toString());case 37:case"end":return e.stop()}}),e)})));return function(t){return e.apply(this,arguments)}}(),_e=function(){var e=Object(y.a)(u.a.mark((function e(t){return u.a.wrap((function(e){for(;;)switch(e.prev=e.next){case 0:return t.preventDefault(),e.next=3,j.createERC20(n,r);case 3:case"end":return e.stop()}}),e)})));return function(t){return e.apply(this,arguments)}}(),Ce=function(){var e=Object(y.a)(u.a.mark((function e(t){var n;return u.a.wrap((function(e){for(;;)switch(e.prev=e.next){case 0:return t.preventDefault(),n=new b.a(w,l,f),e.next=4,n.transfer(h,A);case 4:case"end":return e.stop()}}),e)})));return function(t){return e.apply(this,arguments)}}();return Object(T.jsxs)("div",{className:"cargo",children:[Object(T.jsx)("title",{children:"Deploy ERC20 tokens "}),Object(T.jsxs)("div",{className:"case",children:[Object(T.jsx)("h1",{children:"Deploy an ERC20 token"}),Object(T.jsxs)("form",{className:"form",onSubmit:_e,children:[Object(T.jsxs)("label",{children:[Object(T.jsx)("input",{className:"input",type:"text",name:"name",placeholder:"name (e.g., my token)",onChange:function(e){return i(e.target.value)}}),Object(T.jsx)("input",{className:"input",type:"text",name:"symbol",placeholder:"symbol (e.g., USD)",onChange:function(e){return v(e.target.value)}}),Object(T.jsx)("br",{}),"Name: ",n,Object(T.jsx)("br",{}),"Symbol: ",r]}),Object(T.jsxs)("button",{className:"button",type:"submit",value:"Confirm",children:["Deploy ERC20 token ",r]})]}),Object(T.jsx)("h1",{children:"Transfer ERC20 tokens"}),Object(T.jsxs)("form",{className:"form",onSubmit:Ce,children:[Object(T.jsxs)("label",{children:[Object(T.jsx)("input",{className:"input",type:"text",name:"ercToken",placeholder:"Tokens Address (0x...)",onChange:function(e){return g(e.target.value)}}),Object(T.jsx)("input",{className:"input",type:"text",name:"recipient",placeholder:"Recipient(0x...)",onChange:function(e){return _(e.target.value)}}),Object(T.jsx)("input",{className:"input",type:"number",name:"recipient",placeholder:"transfer Amount",onChange:function(e){return R(e.target.value)}}),Object(T.jsx)("br",{}),"Token: ",w,Object(T.jsx)("br",{}),"Recipient: ",h,Object(T.jsx)("br",{}),"Amount: ",A]}),Object(T.jsxs)("button",{className:"button",type:"submit",value:"Confirm",children:["Transfer ",A]})]}),Object(T.jsx)("h1",{children:"Retrieve Pair Reserve/Circle"}),Object(T.jsxs)("form",{className:"formhigh",onSubmit:he,children:[Object(T.jsxs)("label",{children:[Object(T.jsx)("input",{className:"input",type:"text",name:"pair",placeholder:"Pair Address (0x...)",onChange:function(e){return F(e.target.value)}}),Object(T.jsx)("br",{}),"Pair: ",D,Object(T.jsx)("br",{}),"reserve0: ",B,Object(T.jsx)("br",{}),"reserve1: ",L,Object(T.jsx)("br",{}),"ICO: ",W," \xa0\xa0\xa0 scalar0: ",V," \xa0\xa0\xa0 scalar1: ",ee,"\xa0\xa0\xa0 r: ",ie,Object(T.jsx)("br",{}),"lambda0: ",ue," lambda1: ",le,Object(T.jsx)("br",{}),"mu: ",Te,Object(T.jsx)("br",{}),"token0: ",xe,Object(T.jsx)("br",{}),"token1: ",Me]}),Object(T.jsxs)("button",{className:"button",type:"submit",value:"Confirm",children:["Retrieve ",D]})]})]})]})},x=function(e){e&&e instanceof Function&&n.e(3).then(n.bind(null,96)).then((function(t){var n=t.getCLS,a=t.getFID,i=t.getFCP,s=t.getLCP,p=t.getTTFB;n(e),a(e),i(e),s(e),p(e)}))};p.a.render(Object(T.jsx)(i.a.StrictMode,{children:Object(T.jsx)(v,{})}),document.getElementById("root")),x()}},[[93,1,2]]]);
//# sourceMappingURL=main.bb494f5c.chunk.js.map