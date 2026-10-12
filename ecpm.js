/**
 * Quantumult X rewrite — 纯 JS 实现 AES-256-ECB + MD5，不依赖 CryptoJS
 *
 * [rewrite_local]
 * ^https?:\/\/duanju\.kittypay\.cn\/api\/ad\/create url script-request-body kittypay_ad_create.js
 *
 * [mitm]
 * hostname = duanju.kittypay.cn
 */

// ==================== AES-256 SBOX ====================
var _SBOX = new Uint8Array([
    0x63,0x7c,0x77,0x7b,0xf2,0x6b,0x6f,0xc5,0x30,0x01,0x67,0x2b,0xfe,0xd7,0xab,0x76,
    0xca,0x82,0xc9,0x7d,0xfa,0x59,0x47,0xf0,0xad,0xd4,0xa2,0xaf,0x9c,0xa4,0x72,0xc0,
    0xb7,0xfd,0x93,0x26,0x36,0x3f,0xf7,0xcc,0x34,0xa5,0xe5,0xf1,0x71,0xd8,0x31,0x15,
    0x04,0xc7,0x23,0xc3,0x18,0x96,0x05,0x9a,0x07,0x12,0x80,0xe2,0xeb,0x27,0xb2,0x75,
    0x09,0x83,0x2c,0x1a,0x1b,0x6e,0x5a,0xa0,0x52,0x3b,0xd6,0xb3,0x29,0xe3,0x2f,0x84,
    0x53,0xd1,0x00,0xed,0x20,0xfc,0xb1,0x5b,0x6a,0xcb,0xbe,0x39,0x4a,0x4c,0x58,0xcf,
    0xd0,0xef,0xaa,0xfb,0x43,0x4d,0x33,0x85,0x45,0xf9,0x02,0x7f,0x50,0x3c,0x9f,0xa8,
    0x51,0xa3,0x40,0x8f,0x92,0x9d,0x38,0xf5,0xbc,0xb6,0xda,0x21,0x10,0xff,0xf3,0xd2,
    0xcd,0x0c,0x13,0xec,0x5f,0x97,0x44,0x17,0xc4,0xa7,0x7e,0x3d,0x64,0x5d,0x19,0x73,
    0x60,0x81,0x4f,0xdc,0x22,0x2a,0x90,0x88,0x46,0xee,0xb8,0x14,0xde,0x5e,0x0b,0xdb,
    0xe0,0x32,0x3a,0x0a,0x49,0x06,0x24,0x5c,0xc2,0xd3,0xac,0x62,0x91,0x95,0xe4,0x79,
    0xe7,0xc8,0x37,0x6d,0x8d,0xd5,0x4e,0xa9,0x6c,0x56,0xf4,0xea,0x65,0x7a,0xae,0x08,
    0xba,0x78,0x25,0x2e,0x1c,0xa6,0xb4,0xc6,0xe8,0xdd,0x74,0x1f,0x4b,0xbd,0x8b,0x8a,
    0x70,0x3e,0xb5,0x66,0x48,0x03,0xf6,0x0e,0x61,0x35,0x57,0xb9,0x86,0xc1,0x1d,0x9e,
    0xe1,0xf8,0x98,0x11,0x69,0xd9,0x8e,0x94,0x9b,0x1e,0x87,0xe9,0xce,0x55,0x28,0xdf,
    0x8c,0xa1,0x89,0x0d,0xbf,0xe6,0x42,0x68,0x41,0x99,0x2d,0x0f,0xb0,0x54,0xbb,0x16
]);

var _INV_SBOX = new Uint8Array(256);
(function(){ for (var i = 0; i < 256; i++) _INV_SBOX[_SBOX[i]] = i; })();

var _RCON = [0x01,0x02,0x04,0x08,0x10,0x20,0x40,0x80,0x1b,0x36,0x6c,0xd8,0xab,0x4d];

function _xtime(a){ return ((a << 1) ^ ((a & 0x80) ? 0x1b : 0)) & 0xff; }
function _gmul(a, b){
    var p = 0;
    for (var i = 0; i < 8; i++) {
        if (b & 1) p ^= a;
        var hi = a & 0x80;
        a = (a << 1) & 0xff;
        if (hi) a ^= 0x1b;
        b >>= 1;
    }
    return p;
}

function _keyExpansion256(key){
    var Nk = 8, Nr = 14;
    var totalWords = 4 * (Nr + 1);
    var w = new Uint8Array(totalWords * 4);
    for (var i = 0; i < 32; i++) w[i] = key[i];
    for (var i = Nk; i < totalWords; i++) {
        var t0 = w[(i-1)*4], t1 = w[(i-1)*4+1], t2 = w[(i-1)*4+2], t3 = w[(i-1)*4+3];
        if (i % Nk === 0) {
            var tmp = t0;
            t0 = _SBOX[t1] ^ _RCON[i/Nk - 1];
            t1 = _SBOX[t2];
            t2 = _SBOX[t3];
            t3 = _SBOX[tmp];
        } else if (i % Nk === 4) {
            t0 = _SBOX[t0]; t1 = _SBOX[t1]; t2 = _SBOX[t2]; t3 = _SBOX[t3];
        }
        w[i*4]   = w[(i-Nk)*4]   ^ t0;
        w[i*4+1] = w[(i-Nk)*4+1] ^ t1;
        w[i*4+2] = w[(i-Nk)*4+2] ^ t2;
        w[i*4+3] = w[(i-Nk)*4+3] ^ t3;
    }
    return { w: w, Nr: Nr };
}

function _addRoundKey(s, w, round){ for (var i = 0; i < 16; i++) s[i] ^= w[round*16 + i]; }
function _subBytes(s){ for (var i = 0; i < 16; i++) s[i] = _SBOX[s[i]]; }
function _invSubBytes(s){ for (var i = 0; i < 16; i++) s[i] = _INV_SBOX[s[i]]; }

function _shiftRows(s){
    var t = s[1]; s[1] = s[5]; s[5] = s[9]; s[9] = s[13]; s[13] = t;
    t = s[2]; s[2] = s[10]; s[10] = t;
    t = s[6]; s[6] = s[14]; s[14] = t;
    t = s[15]; s[15] = s[11]; s[11] = s[7]; s[7] = s[3]; s[3] = t;
}
function _invShiftRows(s){
    var t = s[13]; s[13] = s[9]; s[9] = s[5]; s[5] = s[1]; s[1] = t;
    t = s[2]; s[2] = s[10]; s[10] = t;
    t = s[6]; s[6] = s[14]; s[14] = t;
    t = s[3]; s[3] = s[7]; s[7] = s[11]; s[11] = s[15]; s[15] = t;
}
function _mixColumns(s){
    for (var c = 0; c < 4; c++) {
        var i = c * 4;
        var a0 = s[i], a1 = s[i+1], a2 = s[i+2], a3 = s[i+3];
        var x = a0 ^ a1 ^ a2 ^ a3;
        s[i]   = a0 ^ x ^ _xtime(a0 ^ a1);
        s[i+1] = a1 ^ x ^ _xtime(a1 ^ a2);
        s[i+2] = a2 ^ x ^ _xtime(a2 ^ a3);
        s[i+3] = a3 ^ x ^ _xtime(a3 ^ a0);
    }
}
function _invMixColumns(s){
    for (var c = 0; c < 4; c++) {
        var i = c * 4;
        var a0 = s[i], a1 = s[i+1], a2 = s[i+2], a3 = s[i+3];
        s[i]   = _gmul(a0,14) ^ _gmul(a1,11) ^ _gmul(a2,13) ^ _gmul(a3,9);
        s[i+1] = _gmul(a0,9)  ^ _gmul(a1,14) ^ _gmul(a2,11) ^ _gmul(a3,13);
        s[i+2] = _gmul(a0,13) ^ _gmul(a1,9)  ^ _gmul(a2,14) ^ _gmul(a3,11);
        s[i+3] = _gmul(a0,11) ^ _gmul(a1,13) ^ _gmul(a2,9)  ^ _gmul(a3,14);
    }
}
function _encryptBlock(s, w, Nr){
    _addRoundKey(s, w, 0);
    for (var r = 1; r < Nr; r++) { _subBytes(s); _shiftRows(s); _mixColumns(s); _addRoundKey(s, w, r); }
    _subBytes(s); _shiftRows(s); _addRoundKey(s, w, Nr);
}
function _decryptBlock(s, w, Nr){
    _addRoundKey(s, w, Nr);
    for (var r = Nr - 1; r >= 1; r--) { _invShiftRows(s); _invSubBytes(s); _addRoundKey(s, w, r); _invMixColumns(s); }
    _invShiftRows(s); _invSubBytes(s); _addRoundKey(s, w, 0);
}

function aesEcbEncrypt(plaintextBytes, keyBytes){
    var padLen = 16 - (plaintextBytes.length % 16);
    var padded = new Uint8Array(plaintextBytes.length + padLen);
    padded.set(plaintextBytes);
    for (var i = plaintextBytes.length; i < padded.length; i++) padded[i] = padLen;
    var ks = _keyExpansion256(keyBytes);
    var out = new Uint8Array(padded.length);
    for (var i = 0; i < padded.length; i += 16) {
        var s = new Uint8Array(16);
        for (var j = 0; j < 16; j++) s[j] = padded[i + j];
        _encryptBlock(s, ks.w, ks.Nr);
        out.set(s, i);
    }
    return out;
}

function aesEcbDecrypt(cipherBytes, keyBytes){
    if (cipherBytes.length % 16 !== 0) throw new Error("cipher length not multiple of 16: " + cipherBytes.length);
    var ks = _keyExpansion256(keyBytes);
    var out = new Uint8Array(cipherBytes.length);
    for (var i = 0; i < cipherBytes.length; i += 16) {
        var s = new Uint8Array(16);
        for (var j = 0; j < 16; j++) s[j] = cipherBytes[i + j];
        _decryptBlock(s, ks.w, ks.Nr);
        out.set(s, i);
    }
    var padLen = out[out.length - 1];
    if (padLen < 1 || padLen > 16) throw new Error("invalid padding: " + padLen);
    return out.slice(0, out.length - padLen);
}

// ==================== Base64 ====================
var _B64 = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/';

function base64Encode(bytes){
    var r = '', i;
    for (i = 0; i + 2 < bytes.length; i += 3) {
        var n = (bytes[i] << 16) | (bytes[i+1] << 8) | bytes[i+2];
        r += _B64[(n >> 18) & 63] + _B64[(n >> 12) & 63] + _B64[(n >> 6) & 63] + _B64[n & 63];
    }
    if (i + 1 === bytes.length) {
        var n = bytes[i] << 16;
        r += _B64[(n >> 18) & 63] + _B64[(n >> 12) & 63] + '==';
    } else if (i + 2 === bytes.length) {
        var n = (bytes[i] << 16) | (bytes[i+1] << 8);
        r += _B64[(n >> 18) & 63] + _B64[(n >> 12) & 63] + _B64[(n >> 6) & 63] + '=';
    }
    return r;
}

function base64Decode(str){
    str = String(str).replace(/[^A-Za-z0-9+/=]/g, '').replace(/=+$/, '');
    var bytes = [];
    var buf = 0, bits = 0;
    for (var i = 0; i < str.length; i++) {
        var c = _B64.indexOf(str[i]);
        if (c < 0) continue;
        buf = (buf << 6) | c;
        bits += 6;
        if (bits >= 8) { bits -= 8; bytes.push((buf >> bits) & 0xff); }
    }
    return new Uint8Array(bytes);
}

// ==================== UTF-8 ====================
function utf8Encode(str){
    var out = [];
    for (var i = 0; i < str.length; i++) {
        var c = str.charCodeAt(i);
        if (c < 0x80) out.push(c);
        else if (c < 0x800) out.push(0xc0 | (c >> 6), 0x80 | (c & 0x3f));
        else if (c < 0xd800 || c >= 0xe000) out.push(0xe0 | (c >> 12), 0x80 | ((c >> 6) & 0x3f), 0x80 | (c & 0x3f));
        else {
            i++;
            var cp = 0x10000 + (((c & 0x3ff) << 10) | (str.charCodeAt(i) & 0x3ff));
            out.push(0xf0 | (cp >> 18), 0x80 | ((cp >> 12) & 0x3f), 0x80 | ((cp >> 6) & 0x3f), 0x80 | (cp & 0x3f));
        }
    }
    return new Uint8Array(out);
}

function utf8Decode(bytes){
    var s = '', i = 0;
    while (i < bytes.length) {
        var c = bytes[i++];
        if (c < 0x80) s += String.fromCharCode(c);
        else if (c < 0xe0) s += String.fromCharCode(((c & 0x1f) << 6) | (bytes[i++] & 0x3f));
        else if (c < 0xf0) s += String.fromCharCode(((c & 0x0f) << 12) | ((bytes[i++] & 0x3f) << 6) | (bytes[i++] & 0x3f));
        else {
            var cp = ((c & 0x07) << 18) | ((bytes[i++] & 0x3f) << 12) | ((bytes[i++] & 0x3f) << 6) | (bytes[i++] & 0x3f);
            cp -= 0x10000;
            s += String.fromCharCode(0xd800 + (cp >> 10), 0xdc00 + (cp & 0x3ff));
        }
    }
    return s;
}

// ==================== MD5 ====================
var md5 = (function(){
    function safeAdd(x, y){ var lsw = (x & 0xffff) + (y & 0xffff); var msw = (x >> 16) + (y >> 16) + (lsw >> 16); return (msw << 16) | (lsw & 0xffff); }
    function rol(num, cnt){ return (num << cnt) | (num >>> (32 - cnt)); }
    function cmn(q, a, b, x, s, t){ return safeAdd(rol(safeAdd(safeAdd(a, q), safeAdd(x, t)), s), b); }
    function ff(a,b,c,d,x,s,t){ return cmn((b&c)|(~b&d),a,b,x,s,t); }
    function gg(a,b,c,d,x,s,t){ return cmn((b&d)|(c&~d),a,b,x,s,t); }
    function hh(a,b,c,d,x,s,t){ return cmn(b^c^d,a,b,x,s,t); }
    function ii(a,b,c,d,x,s,t){ return cmn(c^(b|~d),a,b,x,s,t); }
    function binlMD5(x, len){
        x[len >> 5] |= 0x80 << (len % 32);
        x[(((len + 64) >>> 9) << 4) + 14] = len;
        var i, olda, oldb, oldc, oldd, a = 1732584193, b = -271733879, c = -1732584194, d = 271733878;
        for (i = 0; i < x.length; i += 16) {
            olda = a; oldb = b; oldc = c; oldd = d;
            a = ff(a,b,c,d,x[i],7,-680876936); d = ff(d,a,b,c,x[i+1],12,-389564586); c = ff(c,d,a,b,x[i+2],17,606105819); b = ff(b,c,d,a,x[i+3],22,-1044525330);
            a = ff(a,b,c,d,x[i+4],7,-176418897); d = ff(d,a,b,c,x[i+5],12,1200080426); c = ff(c,d,a,b,x[i+6],17,-1473231341); b = ff(b,c,d,a,x[i+7],22,-45705983);
            a = ff(a,b,c,d,x[i+8],7,1770035416); d = ff(d,a,b,c,x[i+9],12,-1958414417); c = ff(c,d,a,b,x[i+10],17,-42063); b = ff(b,c,d,a,x[i+11],22,-1990404162);
            a = ff(a,b,c,d,x[i+12],7,1804603682); d = ff(d,a,b,c,x[i+13],12,-40341101); c = ff(c,d,a,b,x[i+14],17,-1502002290); b = ff(b,c,d,a,x[i+15],22,1236535329);
            a = gg(a,b,c,d,x[i+1],5,-165796510); d = gg(d,a,b,c,x[i+6],9,-1069501632); c = gg(c,d,a,b,x[i+11],14,643717713); b = gg(b,c,d,a,x[i],20,-373897302);
            a = gg(a,b,c,d,x[i+5],5,-701558691); d = gg(d,a,b,c,x[i+10],9,38016083); c = gg(c,d,a,b,x[i+15],14,-660478335); b = gg(b,c,d,a,x[i+4],20,-405537848);
            a = gg(a,b,c,d,x[i+9],5,568446438); d = gg(d,a,b,c,x[i+14],9,-1019803690); c = gg(c,d,a,b,x[i+3],14,-187363961); b = gg(b,c,d,a,x[i+8],20,1163531501);
            a = gg(a,b,c,d,x[i+13],5,-1444681467); d = gg(d,a,b,c,x[i+2],9,-51403784); c = gg(c,d,a,b,x[i+7],14,1735328473); b = gg(b,c,d,a,x[i+12],20,-1926607734);
            a = hh(a,b,c,d,x[i+5],4,-378558); d = hh(d,a,b,c,x[i+8],11,-2022574463); c = hh(c,d,a,b,x[i+11],16,1839030562); b = hh(b,c,d,a,x[i+14],23,-35309556);
            a = hh(a,b,c,d,x[i+1],4,-1530992060); d = hh(d,a,b,c,x[i+4],11,1272893353); c = hh(c,d,a,b,x[i+7],16,-155497632); b = hh(b,c,d,a,x[i+10],23,-1094730640);
            a = hh(a,b,c,d,x[i+13],4,681279174); d = hh(d,a,b,c,x[i],11,-358537222); c = hh(c,d,a,b,x[i+3],16,-722521979); b = hh(b,c,d,a,x[i+6],23,76029189);
            a = hh(a,b,c,d,x[i+9],4,-640364487); d = hh(d,a,b,c,x[i+12],11,-421815835); c = hh(c,d,a,b,x[i+15],16,530742520); b = hh(b,c,d,a,x[i+2],23,-995338651);
            a = ii(a,b,c,d,x[i],6,-198630844); d = ii(d,a,b,c,x[i+7],10,1126891415); c = ii(c,d,a,b,x[i+14],15,-1416354905); b = ii(b,c,d,a,x[i+5],21,-57434055);
            a = ii(a,b,c,d,x[i+12],6,1700485571); d = ii(d,a,b,c,x[i+3],10,-1894986606); c = ii(c,d,a,b,x[i+10],15,-1051523); b = ii(b,c,d,a,x[i+1],21,-2054922799);
            a = ii(a,b,c,d,x[i+8],6,1873313359); d = ii(d,a,b,c,x[i+15],10,-30611744); c = ii(c,d,a,b,x[i+6],15,-1560198380); b = ii(b,c,d,a,x[i+13],21,1309151649);
            a = ii(a,b,c,d,x[i+4],6,-145523070); d = ii(d,a,b,c,x[i+11],10,-1120210379); c = ii(c,d,a,b,x[i+2],15,718787259); b = ii(b,c,d,a,x[i+9],21,-343485551);
            a = safeAdd(a, olda); b = safeAdd(b, oldb); c = safeAdd(c, oldc); d = safeAdd(d, oldd);
        }
        return [a, b, c, d];
    }
    function binl2rstr(input){
        var output = '';
        var length32 = input.length * 32;
        for (var i = 0; i < length32; i += 8) output += String.fromCharCode((input[i >> 5] >>> (i % 32)) & 0xff);
        return output;
    }
    function rstr2binl(input){
        var output = [];
        output[(input.length >> 2) - 1] = undefined;
        for (var i = 0; i < output.length; i += 1) output[i] = 0;
        var length8 = input.length * 8;
        for (var i = 0; i < length8; i += 8) output[i >> 5] |= (input.charCodeAt(i / 8) & 0xff) << (i % 32);
        return output;
    }
    function rstr2hex(input){
        var hexTab = '0123456789abcdef';
        var output = '';
        for (var i = 0; i < input.length; i += 1) {
            var x = input.charCodeAt(i);
            output += hexTab.charAt((x >>> 4) & 0x0f) + hexTab.charAt(x & 0x0f);
        }
        return output;
    }
    function str2rstrUTF8(input){
        var bytes = utf8Encode(input);
        var s = '';
        for (var i = 0; i < bytes.length; i++) s += String.fromCharCode(bytes[i]);
        return s;
    }
    return function(s){ return rstr2hex(binl2rstr(binlMD5(rstr2binl(str2rstrUTF8(s)), str2rstrUTF8(s).length * 8))); };
})();

// ==================== 业务逻辑 ====================
var AES_KEY = "376ea147fe4a82431fc8108f6bf6bd3d";
var SIGN_KEY = "0da1a2347f59ac75003140123396816a58383f2c0568e20485381f83cd64a354";

var SIGN_HEADER_NAMES = [
    "appId", "channelId", "clientId", "appVersion",
    "imei", "nonce", "timestamp", "apiVersion", "oaid"
];

function log(msg){ console.log("[KITTYPAY] " + msg); }

function iosJsonStringify(obj){
    if (obj === null || typeof obj !== "object") return JSON.stringify(obj);
    if (Array.isArray(obj)) {
        var arr = [];
        for (var i = 0; i < obj.length; i++) arr.push(iosJsonStringify(obj[i]));
        return "[" + arr.join(",") + "]";
    }
    var keys = Object.keys(obj).sort();
    var parts = [];
    for (var j = 0; j < keys.length; j++) parts.push(JSON.stringify(keys[j]) + ":" + iosJsonStringify(obj[keys[j]]));
    return "{" + parts.join(",") + "}";
}

function aesKeyBytes(){ return utf8Encode(AES_KEY); }

function aesEncrypt(plaintext){
    var bytes = utf8Encode(plaintext);
    var enc = aesEcbEncrypt(bytes, aesKeyBytes());
    return base64Encode(enc);
}

function aesDecrypt(b64){
    var raw = base64Decode(b64);
    var dec = aesEcbDecrypt(raw, aesKeyBytes());
    return utf8Decode(dec);
}

function percentEncodeBase64(b64){
    return b64.replace(/\//g, "%2F").replace(/\+/g, "%2B").replace(/=/g, "%3D");
}

function percentDecode(s){ return decodeURIComponent(s); }

function makeSignature(signHeaders, params){
    var names = Object.keys(signHeaders).sort();
    var canonical = "";
    for (var i = 0; i < names.length; i++) canonical += names[i] + "=" + signHeaders[names[i]] + "&";
    var base = canonical + "key=" + SIGN_KEY;
    var source = iosJsonStringify(params) + "&" + base;
    return md5(source);
}

function main(){
    log("===== triggered =====");
    log("URL: " + ($request.url || "(empty)"));

    var rawBody = $request.body;
    log("body length: " + (rawBody ? rawBody.length : 0));

    if (!rawBody) { log("empty body, passed through"); $done({}); return; }

    var envelope;
    try { envelope = JSON.parse(rawBody); }
    catch (e) { log("body not JSON: " + e.message); $done({}); return; }
    if (!envelope || !envelope.data) { log("missing data field"); $done({}); return; }

    var decrypted;
    var params;
    try {
        decrypted = aesDecrypt(percentDecode(envelope.data));
        log("decrypted (first 200): " + decrypted.substring(0, 200));
        params = JSON.parse(decrypted);
    } catch (e) {
        log("decrypt failed: " + e.message);
        $done({});
        return;
    }

    var oldEcpm = String(params.ecpm);
    var newEcpm = (Math.floor(Math.random() * 100000000) + 100000000) / 1000;
    params.ecpm = newEcpm.toFixed(3);
    log("ecpm " + oldEcpm + " -> " + params.ecpm);

    var newPlaintext = iosJsonStringify(params);
    var newCipherB64 = aesEncrypt(newPlaintext);
    envelope.data = percentEncodeBase64(newCipherB64);
    var newBody = iosJsonStringify(envelope);

    var allHeaders = $request.headers || {};
    var signHeaders = {};
    for (var i = 0; i < SIGN_HEADER_NAMES.length; i++) {
        var name = SIGN_HEADER_NAMES[i];
        var val = allHeaders[name];
        if (val === undefined || val === null || val === "") {
            var lower = name.toLowerCase();
            for (var k in allHeaders) {
                if (allHeaders.hasOwnProperty(k) && k.toLowerCase() === lower) { val = allHeaders[k]; break; }
            }
        }
        if (val !== undefined && val !== null && val !== "") signHeaders[name] = String(val);
    }
    log("sign headers: " + JSON.stringify(signHeaders));

    var newSig = makeSignature(signHeaders, params);
    log("new signature: " + newSig);

    var newHeaders = {};
    for (var hk in allHeaders) if (allHeaders.hasOwnProperty(hk)) newHeaders[hk] = allHeaders[hk];
    newHeaders["signature"] = newSig;

    log("===== done =====");
    $done({ body: newBody, headers: newHeaders });
}

try {
    if (typeof $request !== "undefined") main();
    else $done({});
} catch (e) {
    log("unhandled exception: " + e.message);
    $done({});
}