#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
pmc_client.py — Cliente mínimo RakNet + PocketMine (protocolo MCPE = 84)

Feito a partir da leitura do código-fonte fornecido de:
  - src/raklib/protocol/*  (handshake RakNet: OPEN_CONNECTION_*, ACK/NACK, EncapsulatedPacket, DataPacket)
  - src/raklib/Binary.php  (helpers big/little-endian)
  - src/pocketmine/network/protocol/Info.php (IDs de pacote + protocolo 84)
  - src/pocketmine/network/protocol/LoginPacket.php (formato do login: chain JWT + skin JWT)

IMPORTANTE / LIMITAÇÕES:
  - Este cliente NÃO faz autenticação real com a Xbox Live / Mojang (não temos
    a chave privada da Mojang, nem deveríamos ter). Ele monta uma "chain" JWT
    auto-assinada. Analisando o LoginPacket::decode() do código-fonte fornecido,
    a verificação da assinatura vai falhar (como esperado), MAS o servidor ainda
    extrai displayName/UUID do token mesmo sem verificação bem-sucedida, e o
    código não trava nesse caso.
  - Ou seja: isso só funciona contra servidores que RODAM ESSE FORK (ou fork
    parecido) e que NÃO EXIGEM autenticação Xbox Live verificada (comum em
    servidores privados/antigos rodando protocolo 84, ~MCPE 0.14/0.15).
  - Use apenas contra o SEU PRÓPRIO servidor de testes. Não é um cliente de
    jogo completo — só faz o handshake RakNet + login e mostra o PlayStatus /
    motivo de desconexão que o servidor responder.

Requer apenas a biblioteca padrão do Python (opcionalmente `cryptography`
para gerar/assinar a chave EC384 de forma mais "correta"; sem ela, o script
usa uma assinatura fake, o que — pela análise acima — ainda deve funcionar
para extrair o username em servidores que não fazem enforcement).

Uso:
    python3 pmc_client.py <host> <porta> <username>

Exemplo:
    python3 pmc_client.py 127.0.0.1 19132 TestBot
"""

import base64
import json
import math
import os
import random
import socket
import struct
import sys
import threading
import time
import uuid

MCPE_PROTOCOL = 84
RAKNET_PROTOCOL = 6
RAKNET_MAGIC = bytes([0x00, 0xff, 0xff, 0x00, 0xfe, 0xfe, 0xfe, 0xfe,
                      0xfd, 0xfd, 0xfd, 0xfd, 0x12, 0x34, 0x56, 0x78])

MTU_SIZE = 1400  # tamanho de MTU pedido no handshake

# ---- IDs de pacote (de Info.php / raklib/protocol) ----
ID_UNCONNECTED_PING = 0x01
ID_OPEN_CONNECTION_REQUEST_1 = 0x05
ID_OPEN_CONNECTION_REPLY_1 = 0x06
ID_OPEN_CONNECTION_REQUEST_2 = 0x07
ID_OPEN_CONNECTION_REPLY_2 = 0x08
ID_CLIENT_CONNECT = 0x09
ID_SERVER_HANDSHAKE = 0x10
ID_CLIENT_HANDSHAKE = 0x13
ID_PING = 0x00
ID_PONG = 0x03
ID_UNCONNECTED_PONG = 0x1c
ID_NACK = 0xa0
ID_ACK = 0xc0

PID_LOGIN = 0x01
PID_PLAY_STATUS = 0x02
PID_DISCONNECT = 0x05
PID_BATCH = 0x06
PID_TEXT = 0x07
PID_MOVE_PLAYER = 0x10

TEXT_TYPE_RAW = 0
TEXT_TYPE_CHAT = 1
TEXT_TYPE_TRANSLATION = 2
TEXT_TYPE_POPUP = 3
TEXT_TYPE_TIP = 4
TEXT_TYPE_SYSTEM = 5

PLAY_STATUS_NAMES = {
    0: "LOGIN_SUCCESS",
    1: "LOGIN_FAILED_CLIENT",
    2: "LOGIN_FAILED_SERVER",
    3: "PLAYER_SPAWN",
}

# Reliabilidades (raklib/protocol/PacketReliability.php)
UNRELIABLE = 0
RELIABLE = 2
RELIABLE_ORDERED = 3


# ---------------------------------------------------------------------------
# Helpers binários (espelham raklib/Binary.php)
# ---------------------------------------------------------------------------

def w_byte(v):
    return bytes([v & 0xff])


def w_short(v):
    return struct.pack(">H", v & 0xffff)


def r_short(b):
    return struct.unpack(">H", b)[0]


def w_int(v):
    return struct.pack(">i", v)


def r_int(b):
    return struct.unpack(">i", b)[0]


def w_long(v):
    return struct.pack(">q", v)


def r_long(b):
    return struct.unpack(">q", b)[0]


def w_lint(v):
    return struct.pack("<i", v)


def r_lint(b):
    return struct.unpack("<i", b)[0]


def w_triad(v):
    # 3 bytes big-endian
    return struct.pack(">I", v)[1:]


def r_triad(b):
    return struct.unpack(">I", b"\x00" + b)[0]


def w_ltriad(v):
    # 3 bytes little-endian
    return struct.pack("<I", v)[:3]


def r_ltriad(b):
    return struct.unpack("<I", b + b"\x00")[0]


def w_string(v: bytes):
    return w_short(len(v)) + v


def put_address(addr: str, port: int) -> bytes:
    parts = [(~int(x)) & 0xff for x in addr.split(".")]
    return bytes([4] + parts) + w_short(port)


def dummy_systemaddresses(n=10) -> bytes:
    out = b""
    for _ in range(n):
        out += put_address("0.0.0.0", 0)
    return out


# ---------------------------------------------------------------------------
# EncapsulatedPacket / Datagram (raklib/protocol/EncapsulatedPacket.php + DataPacket.php)
# ---------------------------------------------------------------------------

def make_encapsulated(payload: bytes, reliability=RELIABLE_ORDERED,
                       message_index=0, order_index=0, order_channel=0) -> bytes:
    flags = reliability << 5
    out = w_byte(flags)
    out += w_short(len(payload) << 3)  # comprimento em BITS, big-endian short
    if reliability > UNRELIABLE:
        if reliability >= RELIABLE:  # inclui RELIABLE e RELIABLE_ORDERED
            out += w_ltriad(message_index)
        if reliability <= 4 and reliability != RELIABLE:
            out += w_ltriad(order_index) + w_byte(order_channel)
    out += payload
    return out


def make_datagram(seq_number: int, encapsulated_list) -> bytes:
    out = w_byte(0x80)  # bit de "é um datagrama" (não ACK/NACK)
    out += w_ltriad(seq_number)
    for enc in encapsulated_list:
        out += enc
    return out


def parse_encapsulated(buf: bytes, offset: int):
    """Analisa UM pacote encapsulado a partir de offset.

    Retorna (info, novo_offset), onde info é um dict com:
      - buffer: bytes do fragmento (payload cru dessa parte)
      - has_split, split_count, split_id, split_index (quando has_split=True)
    """
    flags = buf[offset]
    reliability = (flags & 0b11100000) >> 5
    has_split = (flags & 0b00010000) > 0
    length_bits = r_short(buf[offset + 1:offset + 3])
    length = (length_bits + 7) // 8
    off = offset + 3

    if reliability > UNRELIABLE:
        if reliability >= RELIABLE and reliability != 5:  # != UNRELIABLE_WITH_ACK_RECEIPT
            off += 3  # messageIndex
        if reliability <= 4 and reliability != RELIABLE:
            off += 3 + 1  # orderIndex + orderChannel

    info = {"has_split": has_split, "split_count": None, "split_id": None, "split_index": None}
    if has_split:
        info["split_count"] = r_int(buf[off:off + 4]); off += 4
        info["split_id"] = r_short(buf[off:off + 2]); off += 2
        info["split_index"] = r_int(buf[off:off + 4]); off += 4

    info["buffer"] = buf[off:off + length]
    off += length
    return info, off


def classify_header(byte: int) -> str:
    """Classifica o byte de cabeçalho de um pacote 'conectado' do RakLib.

    Esquema usado neste fork (confirmado por ACK.php=0xc0 e NACK.php=0xa0):
      100xxxxx (0x80-0x9F) -> pacote de dados (datagrama com encapsulados)
      101xxxxx (0xA0-0xBF) -> NACK
      110xxxxx (0xC0-0xDF) -> ACK
    Qualquer outra coisa (ex: 0xFE) não é um pacote 'conectado' válido deste
    esquema e deve ser ignorado/reportado, nunca parseado como datagrama.
    """
    top3 = byte & 0xE0
    if top3 == 0xC0:
        return "ack"
    if top3 == 0xA0:
        return "nack"
    if top3 == 0x80:
        return "data"
    return "unknown"


def make_ack(seq_numbers) -> bytes:
    """Monta um pacote ACK simples (um record por sequência, sem faixas)."""
    out = w_byte(ID_ACK)
    out += w_short(len(seq_numbers))
    for seq in seq_numbers:
        out += w_byte(1)  # 1 = registro único (não é faixa min..max)
        out += w_ltriad(seq)
    return out


# ---------------------------------------------------------------------------
# JWT (chain de login) — sem validação real da Mojang, ver aviso no topo
# ---------------------------------------------------------------------------

def b64url(data: bytes) -> str:
    """Base64 padrão (NÃO url-safe).

    Nota: analisando LoginPacket::decode() -> decodeToken(), o PHP faz
    `base64_decode($payloadB64)` SEM converter '-'/'_' para '+'/'/' (só faz
    essa troca para o campo de assinatura). Ou seja, esse decoder específico
    espera base64 padrão no header/payload, não base64url (apesar do padrão
    JWT normalmente usar base64url). Usar urlsafe aqui corrompe o payload
    silenciosamente do lado do servidor.
    """
    return base64.b64encode(data).decode()


def try_sign_es384(message: bytes):
    """Tenta assinar com ES384 usando `cryptography`, se disponível.
    Retorna (assinatura_raw_96_bytes, pubkey_der_base64) ou (None, None)."""
    try:
        from cryptography.hazmat.primitives.asymmetric import ec
        from cryptography.hazmat.primitives import hashes, serialization
        from cryptography.hazmat.primitives.asymmetric.utils import decode_dss_signature

        priv = ec.generate_private_key(ec.SECP384R1())
        pub_der = priv.public_key().public_bytes(
            serialization.Encoding.DER,
            serialization.PublicFormat.SubjectPublicKeyInfo,
        )
        der_sig = priv.sign(message, ec.ECDSA(hashes.SHA384()))
        r, s = decode_dss_signature(der_sig)
        raw_sig = r.to_bytes(48, "big") + s.to_bytes(48, "big")
        return raw_sig, base64.b64encode(pub_der).decode()
    except Exception:
        return None, None


def build_login_chain(username: str, client_uuid: str):
    """Monta o token JWT (header.payload.signature) usado como 'chain'."""
    now = int(time.time())

    header = {"alg": "ES384", "typ": "JWT"}
    payload = {
        "extraData": {
            "displayName": username,
            "identity": client_uuid,
        },
        "nbf": now - 3600,
        "exp": now + 3600,
        "iat": now,
    }

    header_b64 = b64url(json.dumps(header).encode())
    payload_b64 = b64url(json.dumps(payload).encode())
    message = f"{header_b64}.{payload_b64}".encode()

    sig_raw, pubkey_b64 = try_sign_es384(message)
    if sig_raw is None:
        # Sem `cryptography` instalado: assinatura fake (96 bytes de zero).
        # A verificação no servidor vai falhar de qualquer forma (não temos a
        # chave privada da Mojang), então isso não piora nada.
        sig_raw = b"\x00" * 96
        pubkey_b64 = "AAAA"  # placeholder

    payload["identityPublicKey"] = pubkey_b64
    payload_b64 = b64url(json.dumps(payload).encode())
    message = f"{header_b64}.{payload_b64}".encode()
    sig_raw2, _ = (sig_raw, pubkey_b64)  # não re-assinamos por simplicidade

    sig_b64 = b64url(sig_raw2)
    token = f"{header_b64}.{payload_b64}.{sig_b64}"
    return token


def build_skin_token(client_id: int, server_address: str):
    header_b64 = b64url(json.dumps({"alg": "none"}).encode())
    # skin 64x32 branca (RGBA), só para preencher o campo
    skin_bytes = bytes([255, 255, 255, 255]) * (64 * 32)
    payload = {
        "ClientRandomId": client_id,
        "ServerAddress": server_address,
        "SkinId": "Standard_Custom",
        "SkinData": base64.b64encode(skin_bytes).decode(),
    }
    payload_b64 = b64url(json.dumps(payload).encode())
    sig_b64 = b64url(b"\x00" * 32)
    return f"{header_b64}.{payload_b64}.{sig_b64}"


def build_text_packet_bytes(username: str, message: str) -> bytes:
    """TextPacket, tipo TYPE_CHAT (1): byte(type) + string(source) + string(message).
    Uma mensagem começando com '/' é tratada pelo servidor como comando."""
    body = (bytes([TEXT_TYPE_CHAT])
            + w_string(username.encode("utf-8"))
            + w_string(message.encode("utf-8")))
    return bytes([PID_TEXT]) + body


def build_move_player_packet_bytes(eid: int, x: float, y: float, z: float,
                                    yaw: float, body_yaw: float, pitch: float,
                                    mode: int = 0, on_ground: bool = True) -> bytes:
    """MovePlayerPacket (0x10): eid(long) + x,y,z,yaw,bodyYaw,pitch(float) +
    mode(byte) + onGround(byte). Nota: 'y' aqui é a altura dos OLHOS, não dos
    pés — o servidor subtrai getEyeHeight() pra achar a posição real."""
    body = (w_long(eid)
            + struct.pack(">f", x)
            + struct.pack(">f", y)
            + struct.pack(">f", z)
            + struct.pack(">f", yaw)
            + struct.pack(">f", body_yaw)
            + struct.pack(">f", pitch)
            + w_byte(mode)
            + w_byte(1 if on_ground else 0))
    return bytes([PID_MOVE_PLAYER]) + body


def build_login_packet_bytes(username: str, server_address: str, debug=False) -> bytes:
    import zlib

    client_uuid = str(uuid.uuid4())
    client_id = int.from_bytes(os.urandom(8), "big", signed=True)

    chain_token = build_login_chain(username, client_uuid)
    chain_json = json.dumps({"chain": [chain_token]}).encode()

    skin_token = build_skin_token(client_id, server_address).encode()

    inner = w_lint(len(chain_json)) + chain_json + w_lint(len(skin_token)) + skin_token
    compressed = zlib.compress(inner)

    if debug:
        print(f"[debug] chain_json ({len(chain_json)} bytes): {chain_json[:200]}...")
        print(f"[debug] skin_token ({len(skin_token)} bytes): {skin_token[:200]}...")
        print(f"[debug] inner (descomprimido, {len(inner)} bytes)")
        print(f"[debug] compressed (zlib, {len(compressed)} bytes)")
        # Auto-verificação: refaz o processo inverso pra garantir que está consistente
        redecompressed = zlib.decompress(compressed)
        assert redecompressed == inner, "BUG: zlib não é reversível!"
        off = 0
        chain_len = r_lint(redecompressed[off:off + 4]); off += 4
        chain_check = redecompressed[off:off + chain_len]; off += chain_len
        skin_len = r_lint(redecompressed[off:off + 4]); off += 4
        skin_check = redecompressed[off:off + skin_len]; off += skin_len
        print(f"[debug] auto-check chain_len={chain_len} bytes_lidos={len(chain_check)} ok={chain_check == chain_json}")
        print(f"[debug] auto-check skin_len={skin_len} bytes_lidos={len(skin_check)} ok={skin_check == skin_token}")

    body = w_int(MCPE_PROTOCOL) + w_int(len(compressed)) + compressed
    return bytes([PID_LOGIN]) + body


# ---------------------------------------------------------------------------
# Cliente
# ---------------------------------------------------------------------------

class PMClient:
    def __init__(self, host, port, username, source_ip=None):
        self.host = host
        self.port = port
        self.username = username
        self.source_ip = source_ip
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        if source_ip:
            # IP aliasing: liga o socket a um IP local específico (precisa já
            # existir na interface de rede, ex: `ip addr add <ip>/24 dev eth0`).
            # Cada bot "sai" com um IP de origem diferente na LAN, driblando
            # limites de taxa por-IP como o packetLimit do RakLib.
            self.sock.bind((source_ip, 0))
        self.sock.settimeout(5)
        self.client_id = int.from_bytes(os.urandom(8), "big", signed=True) & 0x7fffffffffffffff
        self.seq_send = 0
        self.msg_index = 0
        self.order_index = 0
        self.server_id = None
        self.mtu = MTU_SIZE
        self.debug = False
        self.running = False
        self._keepalive_thread = None
        self._send_lock = threading.Lock()
        self.status = "idle"  # idle -> connecting -> connected -> disconnected/failed
        self.error = None
        self.disconnect_reason = None
        self.quiet = False  # suprime prints individuais (usado no modo swarm)
        self.split_buffers = {}  # split_id -> {index: bytes}

        # Movimento (caminhada aleatória opcional)
        self.eye_height = 1.62
        self.spawn_x = 128.5
        self.spawn_y_foot = 63.0
        self.spawn_z = 128.5
        self.walk_radius = 8.0
        self.pos_x = self.spawn_x
        self.pos_z = self.spawn_z
        self.yaw = 0.0
        self._move_thread = None
        self.server_forced_pos = None  # (x_eye, y_eye, z, yaw, pitch) — última posição que o servidor nos mandou de volta

    # -- envio de baixo nível --

    def _log(self, msg):
        if not self.quiet:
            print(msg)

    def _send_raw(self, data: bytes):
        self.sock.sendto(data, (self.host, self.port))

    def _send_datagram(self, encapsulated_payloads, reliability=RELIABLE_ORDERED):
        with self._send_lock:
            encs = []
            for payload in encapsulated_payloads:
                if reliability == RELIABLE_ORDERED:
                    enc = make_encapsulated(
                        payload,
                        reliability=RELIABLE_ORDERED,
                        message_index=self.msg_index,
                        order_index=self.order_index,
                        order_channel=0,
                    )
                    self.msg_index += 1
                    self.order_index += 1
                elif reliability > UNRELIABLE:
                    enc = make_encapsulated(
                        payload,
                        reliability=reliability,
                        message_index=self.msg_index,
                    )
                    self.msg_index += 1
                else:
                    # UNRELIABLE não carrega campo messageIndex no formato binário
                    # (ver make_encapsulated) — NÃO se deve consumir/incrementar o
                    # contador aqui, senão os índices dos pacotes RELIABLE/
                    # RELIABLE_ORDERED seguintes ficam fora de sequência do ponto
                    # de vista do servidor, que passa a bufferizá-los indefinidamente
                    # (ver Session::handleEncapsulatedPacket -> $this->reliableWindow).
                    enc = make_encapsulated(payload, reliability=reliability)
                encs.append(enc)
            dgm = make_datagram(self.seq_send, encs)
            self.seq_send += 1
            self._send_raw(dgm)

    def _recv(self, timeout=5):
        self.sock.settimeout(timeout)
        try:
            data, _ = self.sock.recvfrom(4096)
            if self.debug:
                preview = data.hex()
                if len(preview) > 120:
                    preview = preview[:120] + "..."
                print(f"[debug] <<< recebido ({len(data)} bytes): {preview}")
            return data
        except socket.timeout:
            return None

    # -- handshake offline --

    def open_connection_request_1(self):
        pkt = w_byte(ID_OPEN_CONNECTION_REQUEST_1) + RAKNET_MAGIC + w_byte(RAKNET_PROTOCOL)
        pkt += b"\x00" * (self.mtu - 18)
        self._send_raw(pkt)
        resp = self._recv()
        if resp is None or resp[0] != ID_OPEN_CONNECTION_REPLY_1:
            raise RuntimeError(f"Sem resposta válida ao OPEN_CONNECTION_REQUEST_1 (recebido: {resp[:1] if resp else None})")
        off = 1 + 16  # id + magic
        self.server_id = r_long(resp[off:off + 8])
        off += 8 + 1  # long + security byte
        self.mtu = r_short(resp[off:off + 2])
        self._log(f"[raknet] OPEN_CONNECTION_REPLY_1 ok — serverID={self.server_id} mtu={self.mtu}")

    def open_connection_request_2(self):
        pkt = w_byte(ID_OPEN_CONNECTION_REQUEST_2) + RAKNET_MAGIC
        pkt += put_address(self.host, self.port)
        pkt += w_short(self.mtu)
        pkt += w_long(self.client_id)
        self._send_raw(pkt)
        resp = self._recv()
        if resp is None or resp[0] != ID_OPEN_CONNECTION_REPLY_2:
            raise RuntimeError(f"Sem resposta válida ao OPEN_CONNECTION_REQUEST_2 (recebido: {resp[:1] if resp else None})")
        self._log("[raknet] OPEN_CONNECTION_REPLY_2 ok — conexão de baixo nível estabelecida")

    # -- handshake "online" --

    def send_client_connect(self):
        payload = (bytes([ID_CLIENT_CONNECT])
                   + w_long(self.client_id)
                   + w_long(int(time.time() * 1000))
                   + w_byte(0))  # useSecurity = false
        self._send_datagram([payload], reliability=RELIABLE)
        self._log("[raknet] CLIENT_CONNECT enviado")

    def send_client_handshake(self, echo_ping, echo_pong):
        payload = bytes([ID_CLIENT_HANDSHAKE])
        payload += put_address(self.host, self.port)
        payload += dummy_systemaddresses(10)
        payload += w_long(echo_ping)
        payload += w_long(echo_pong)
        self._send_datagram([payload], reliability=RELIABLE)
        self._log("[raknet] CLIENT_HANDSHAKE enviado")

    def wait_for_server_handshake(self):
        """Espera o datagrama contendo SERVER_HANDSHAKE_DataPacket (0x10)."""
        deadline = time.time() + 5
        while time.time() < deadline:
            data = self._recv(timeout=2)
            if data is None:
                continue
            kind = classify_header(data[0])
            if kind != "data":
                if self.debug:
                    print(f"[debug] pacote ignorado (tipo={kind}, header=0x{data[0]:02x})")
                continue  # ACK/NACK/desconhecido: não é um datagrama de dados
            seq = r_ltriad(data[1:4])
            self._send_raw(make_ack([seq]))
            off = 4
            while off < len(data):
                info, off = parse_encapsulated(data, off)
                payload = info["buffer"]
                if info["has_split"] or not payload:
                    break
                if payload[0] == ID_SERVER_HANDSHAKE:
                    ping, pong = self._parse_server_handshake(payload)
                    return ping, pong
        raise RuntimeError("Timeout esperando SERVER_HANDSHAKE do servidor")

    @staticmethod
    def _parse_server_handshake(payload: bytes):
        # id(1) + address(1+4+2) + short(2, reservado) + 10x address(7) + long + long
        off = 1
        off += 7  # address do cliente (visto pelo servidor)
        off += 2  # campo extra
        off += 7 * 10  # systemAddresses
        send_ping = r_long(payload[off:off + 8]); off += 8
        send_pong = r_long(payload[off:off + 8]); off += 8
        return send_ping, send_pong

    # -- login MCPE --

    # -- keep-alive --

    def send_ping(self):
        """Envia PING_DataPacket (raklib, id=0x00) pra manter a sessão viva.

        Session::update() do servidor derruba a conexão se não receber NENHUM
        pacote nosso por mais de 10s (ver Session.php: isActive/lastUpdate).
        Como esse é um pacote 'interno' do RakLib (id < 0x80), ele não passa
        pelo prefixo 0xFE nem participa da sequência reliable/ordered do jogo.
        """
        ping_id = int(time.time() * 1000) & 0x7fffffffffffffff
        payload = bytes([ID_PING]) + w_long(ping_id)
        self._send_datagram([payload], reliability=UNRELIABLE)
        if self.debug:
            print(f"[debug] PING enviado (pingID={ping_id})")

    def _keepalive_loop(self, interval=4.0):
        while self.running:
            try:
                self.send_ping()
            except OSError:
                break
            time.sleep(interval)

    def start_keepalive(self, interval=4.0):
        self.running = True
        self._keepalive_thread = threading.Thread(
            target=self._keepalive_loop, args=(interval,), daemon=True
        )
        self._keepalive_thread.start()

    def stop(self):
        self.running = False

    def send_text(self, message: str):
        """Envia uma mensagem de chat (ou comando, se começar com '/')."""
        text_bytes = build_text_packet_bytes(self.username, message)
        wrapped = bytes([0xFE]) + text_bytes  # mesmo motivo do LoginPacket: pid < 0x80
        self._send_datagram([wrapped], reliability=RELIABLE_ORDERED)
        if self.debug:
            print(f"[debug] TextPacket enviado: {message!r}")

    # -- movimento (caminhada aleatória) --

    def send_move(self, x, y_foot, z, yaw, on_ground=True):
        y_eye = y_foot + self.eye_height
        payload = build_move_player_packet_bytes(0, x, y_eye, z, yaw, yaw, 0.0, mode=0, on_ground=on_ground)
        wrapped = bytes([0xFE]) + payload
        # UNRELIABLE: perder um update de posição não importa, o próximo já
        # substitui — e assim não interfere no messageIndex/orderIndex usado
        # pelos pacotes RELIABLE_ORDERED (login/chat).
        self._send_datagram([wrapped], reliability=UNRELIABLE)
        if self.debug:
            print(f"[debug] MOVE enviado x={x:.2f} y_foot={y_foot:.2f} z={z:.2f} yaw={yaw:.1f}")

    def _movement_loop(self, interval=0.35, step=0.25):
        target_angle = random.uniform(0, 2 * 3.14159265)
        ticks_until_new_target = 0
        while self.running:
            if ticks_until_new_target <= 0:
                target_angle = random.uniform(0, 2 * 3.14159265)
                ticks_until_new_target = random.randint(6, 20)
            ticks_until_new_target -= 1

            new_x = self.pos_x + math.cos(target_angle) * step
            new_z = self.pos_z + math.sin(target_angle) * step

            # mantém dentro do raio de passeio ao redor do spawn
            dx = new_x - self.spawn_x
            dz = new_z - self.spawn_z
            if (dx * dx + dz * dz) ** 0.5 > self.walk_radius:
                target_angle = math.atan2(self.spawn_z - self.pos_z, self.spawn_x - self.pos_x)
                ticks_until_new_target = random.randint(6, 20)
                new_x = self.pos_x + math.cos(target_angle) * step
                new_z = self.pos_z + math.sin(target_angle) * step

            self.pos_x, self.pos_z = new_x, new_z
            self.yaw = (-math.degrees(target_angle) + 90) % 360  # yaw MCPE: 0=+Z, sentido horário

            try:
                self.send_move(self.pos_x, self.spawn_y_foot, self.pos_z, self.yaw)
            except Exception as e:
                if self.debug:
                    import traceback
                    traceback.print_exc()
                self.error = f"movimento: {e}"
                break
            time.sleep(interval)
        if self.debug:
            print("[debug] thread de movimento encerrada")

    def _wait_and_start_movement(self, timeout=180):
        """Espera o servidor confirmar o spawn de verdade (chunks carregados,
        $spawned=true no Player.php) antes de começar a andar — mandar
        movimento antes disso só é revertido pelo servidor (forceMovement)."""
        self._log("[cliente] aguardando spawn completo (carregamento de chunks) antes de andar...")
        start = time.time()
        while self.running and (time.time() - start) < timeout:
            if self.status == "connected":
                self._log(f"[cliente] spawn confirmado após {time.time()-start:.1f}s")
                break
            time.sleep(0.5)
        else:
            if self.running:
                self._log("[cliente] spawn não confirmado dentro do tempo limite — tentando andar assim mesmo")

        if not self.running:
            return

        # IMPORTANTE: mesmo após o spawn, o servidor deixa $forceMovement
        # apontando pra posição de spawn (ver Player::checkTeleportPosition).
        # O PRIMEIRO MovePlayerPacket que mandarmos precisa estar bem perto
        # dessa posição (<~0.32 blocos) pra ser aceito e limpar forceMovement
        # de vez — senão o servidor reverte pra sempre. Usamos a última
        # posição que o próprio servidor nos mandou como âncora exata.
        if self.server_forced_pos:
            x, y_eye, z, yaw, pitch = self.server_forced_pos
            y_foot = y_eye - self.eye_height
            self._log(f"[cliente] confirmando posição de spawn ({x:.2f},{y_foot:.2f},{z:.2f})")
            for _ in range(3):
                self.send_move(x, y_foot, z, yaw)
                time.sleep(0.3)
            self.spawn_x, self.spawn_y_foot, self.spawn_z = x, y_foot, z
            self.pos_x, self.pos_z = x, z
            self.yaw = yaw
        else:
            self._log("[cliente] nenhuma posição de spawn recebida do servidor — usando padrão/--spawn")

        self.start_movement()

    def start_movement(self, interval=0.35, step=0.25):
        self._move_thread = threading.Thread(
            target=self._movement_loop, args=(interval, step), daemon=True
        )
        self._move_thread.start()
        self._log(f"[cliente] movimento iniciado (spawn={self.spawn_x},{self.spawn_y_foot},{self.spawn_z} raio={self.walk_radius})")

    def send_login(self):
        server_addr = f"{self.host}:{self.port}"
        login_bytes = build_login_packet_bytes(self.username, server_addr, debug=self.debug)
        # IMPORTANTE: Session.php (raklib) trata qualquer pacote cujo primeiro
        # byte seja < 0x80 como um pacote INTERNO do próprio RakLib (handshake,
        # ping, disconnect) e nunca repassa pra camada do jogo (PocketMine).
        # Pacotes MCPE (Login=0x01, PlayStatus=0x02, ...) têm pid < 0x80, então
        # precisam ser prefixados com 0xFE — exatamente como o próprio servidor
        # faz ao enviar (RakLibInterface::putPacket -> chr(0xfe).$packet->buffer).
        # getPacket() do lado do servidor desfaz esse prefixo automaticamente.
        wrapped = bytes([0xFE]) + login_bytes
        if self.debug:
            print(f"[debug] LoginPacket completo ({len(login_bytes)} bytes, +0xFE={len(wrapped)}): {wrapped[:60].hex()}...")
        self._send_datagram([wrapped], reliability=RELIABLE_ORDERED)
        self._log(f"[mcpe] LoginPacket enviado (username={self.username}, protocolo={MCPE_PROTOCOL})")

    def read_loop(self, seconds=None):
        """Escuta pacotes recebidos indefinidamente (até self.running=False),
        ou por `seconds` segundos se informado."""
        deadline = None if seconds is None else time.time() + seconds
        while self.running and (deadline is None or time.time() < deadline):
            data = self._recv(timeout=2)
            if data is None:
                continue
            kind = classify_header(data[0])
            if kind != "data":
                if self.debug:
                    print(f"[debug] pacote ignorado (tipo={kind}, header=0x{data[0]:02x})")
                continue  # ACK/NACK/desconhecido: ignorado aqui
            seq = r_ltriad(data[1:4])
            self._send_raw(make_ack([seq]))
            off = 4
            while off < len(data):
                try:
                    info, off = parse_encapsulated(data, off)
                except Exception:
                    break
                if not info["buffer"] and not info["has_split"]:
                    break
                self._process_encapsulated(info)

    def _process_encapsulated(self, info):
        """Recebe o dict retornado por parse_encapsulated. Se for um fragmento
        de split, acumula e só chama _handle_game_payload quando todos os
        fragmentos tiverem chegado (remontados na ordem correta)."""
        if not info["has_split"]:
            if info["buffer"]:
                self._handle_game_payload(info["buffer"])
            return

        sid = info["split_id"]
        idx = info["split_index"]
        count = info["split_count"]
        bucket = self.split_buffers.setdefault(sid, {})
        bucket[idx] = info["buffer"]

        if self.debug:
            print(f"[debug] fragmento recebido splitID={sid} {len(bucket)}/{count}")

        if len(bucket) >= count:
            full = b"".join(bucket[i] for i in range(count))
            del self.split_buffers[sid]
            if self.debug:
                print(f"[debug] pacote remontado ({len(full)} bytes) a partir de {count} fragmentos")
            self._handle_game_payload(full)

    def _handle_game_payload(self, payload: bytes):
        if len(payload) >= 1 and payload[0] == 0xFE:
            # Mesma lógica do RakLibInterface::getPacket() do lado do servidor:
            # pacotes do jogo vêm prefixados com 0xFE; o pid de verdade é o
            # byte seguinte.
            payload = payload[1:]
        if len(payload) == 0:
            return
        pid = payload[0]
        if pid == PID_PLAY_STATUS:
            status = r_int(payload[1:5])
            name = PLAY_STATUS_NAMES.get(status, f"desconhecido({status})")
            self._log(f"[mcpe] PlayStatus recebido: {name}")
            if status == 3:  # PLAYER_SPAWN — só agora $this->spawned é true de fato
                self.status = "connected"
            elif status == 0:  # LOGIN_SUCCESS — login aceito, mas ainda carregando chunks
                self.status = "login_ok"
            elif status in (1, 2):  # LOGIN_FAILED_CLIENT/SERVER
                self.status = "failed"
                self.error = name
                self.running = False
        elif pid == PID_DISCONNECT:
            # Nota: isso cobre o DisconnectPacket da CAMADA DO JOGO (kick com
            # mensagem legível, formato hide(1)+tamanho(1 byte)+msg, visto no
            # caso "Login timeout"). Uma desconexão de baixo nível do próprio
            # RakLib (ex: timeout de sessão) tem outro formato binário sem
            # mensagem legível — nesse caso a validação abaixo descarta o
            # texto ao invés de mostrar bytes ilegíveis.
            msg = None
            try:
                hide = payload[1]
                msg_len = payload[2]
                candidate = payload[3:3 + msg_len].decode("utf-8")
                printable = sum(1 for ch in candidate if ch.isprintable())
                if candidate and printable / len(candidate) > 0.9:
                    msg = candidate
            except Exception:
                pass
            if msg:
                self._log(f"[mcpe] DISCONNECT recebido — mensagem: {msg!r}")
            else:
                msg = "(desconexão de baixo nível / sem mensagem legível)"
                self._log(f"[mcpe] DISCONNECT/timeout de baixo nível recebido (payload cru): {payload.hex()}")
            self.disconnect_reason = msg
            self.status = "disconnected"
            self.running = False
        elif pid == PID_BATCH:
            self._log(f"[mcpe] BatchPacket recebido ({len(payload)} bytes) — parsing de sub-pacotes não implementado neste script")
        elif pid == PID_TEXT:
            try:
                ttype = payload[1]
                off = 2
                source = None
                if ttype in (TEXT_TYPE_CHAT, TEXT_TYPE_POPUP):
                    slen = r_short(payload[off:off + 2]); off += 2
                    source = payload[off:off + slen].decode(errors="replace"); off += slen
                mlen = r_short(payload[off:off + 2]); off += 2
                message = payload[off:off + mlen].decode(errors="replace"); off += mlen
                params = []
                if ttype == TEXT_TYPE_TRANSLATION:
                    count = payload[off]; off += 1
                    for _ in range(count):
                        plen = r_short(payload[off:off + 2]); off += 2
                        params.append(payload[off:off + plen].decode(errors="replace"))
                        off += plen
                if ttype == TEXT_TYPE_TRANSLATION:
                    joined = ", ".join(params)
                    self._log(f"[chat] (traduzido, sem lang file) {message} [{joined}]")
                elif source:
                    self._log(f"[chat] <{source}> {message}")
                else:
                    self._log(f"[chat] {message}")
            except Exception:
                self._log(f"[mcpe] TextPacket recebido (payload cru): {payload.hex()}")
        elif pid == PID_MOVE_PLAYER:
            try:
                body = payload[1:]
                x, y, z, yaw, body_yaw, pitch = struct.unpack(">6f", body[8:32])
                self.server_forced_pos = (x, y, z, yaw, pitch)
                if self.debug:
                    print(f"[debug] MOVE (servidor) x={x:.2f} y={y:.2f} z={z:.2f} yaw={yaw:.1f}")
            except Exception:
                pass
        elif pid == ID_PONG:
            if self.debug:
                print("[raknet] PONG recebido (conexão viva)")
        else:
            self._log(f"[mcpe] pacote id=0x{pid:02x} recebido ({len(payload)} bytes)")

    # -- fluxo completo --

    def connect_and_login(self, interactive=True, move=False):
        self.status = "connecting"
        self.open_connection_request_1()
        self.open_connection_request_2()
        self.send_client_connect()
        ping, pong = self.wait_for_server_handshake()
        self.send_client_handshake(ping, pong)
        time.sleep(0.2)
        self.running = True
        self.send_login()
        self.start_keepalive(interval=4.0)
        if move:
            self.pos_x, self.pos_z = self.spawn_x, self.spawn_z
            self._pending_move = True
            watcher = threading.Thread(target=self._wait_and_start_movement, daemon=True)
            watcher.start()

        receiver = threading.Thread(target=self.read_loop, kwargs={"seconds": None}, daemon=True)
        receiver.start()

        self._log("[cliente] conectado — mantendo sessão viva")
        if interactive:
            print("[cliente] digite mensagens/comandos (ex: /list) e ENTER. Ctrl+C ou /quit para sair.")
            try:
                while self.running:
                    try:
                        line = input()
                    except EOFError:
                        break
                    if not line:
                        continue
                    if line.strip() in ("/quit", "/exit"):
                        break
                    self.send_text(line)
            except KeyboardInterrupt:
                pass
        else:
            try:
                while self.running:
                    time.sleep(0.5)
            except KeyboardInterrupt:
                pass

        self.stop()


def parse_source_ips(spec: str):
    """Aceita formatos como:
      "192.168.1.101,192.168.1.102"
      "192.168.1.101-120"          (faixa no último octeto)
      "192.168.1.101-105,192.168.1.200"   (combinação dos dois)
    Retorna uma lista de strings de IP.
    """
    ips = []
    for part in spec.split(","):
        part = part.strip()
        if "-" in part and part.count(".") == 3:
            base, end = part.rsplit("-", 1)
            prefix, last = base.rsplit(".", 1)
            start_n = int(last)
            end_n = int(end)
            for n in range(start_n, end_n + 1):
                ips.append(f"{prefix}.{n}")
        elif part:
            ips.append(part)
    return ips


def run_swarm(host, port, count, prefix="Bot", ramp_delay=0.3, debug=False,
              hold_seconds=None, move=False, spawn=None, source_ips=None):
    """Sobe `count` clientes em paralelo (cada um com login próprio) pra
    testar quantas conexões o servidor aguenta. Cada bot roda em sua própria
    thread, com handshake RakNet + login + keep-alive independentes."""

    clients = []
    threads = []

    def worker(client):
        try:
            client.connect_and_login(interactive=False, move=move)
        except Exception as e:
            client.status = "failed"
            client.error = str(e)
            client.running = False

    print(f"[swarm] subindo {count} bots contra {host}:{port} (intervalo entre spawns: {ramp_delay}s)"
          + (" [movimento ativado]" if move else "")
          + (f" [{len(source_ips)} IPs de origem em round-robin]" if source_ips else ""))
    for i in range(count):
        username = f"{prefix}{i+1}"
        src_ip = source_ips[i % len(source_ips)] if source_ips else None
        try:
            c = PMClient(host, port, username, source_ip=src_ip)
        except OSError as e:
            print(f"[swarm] falha ao criar socket com IP de origem {src_ip}: {e}")
            print("[swarm] esse IP provavelmente não está configurado na interface de rede "
                  "(ex: falta rodar `ip addr add <ip>/24 dev <interface>`)")
            continue
        c.quiet = not debug
        c.debug = debug
        if spawn:
            c.spawn_x, c.spawn_y_foot, c.spawn_z = spawn
        clients.append(c)
        t = threading.Thread(target=worker, args=(c,), daemon=True)
        threads.append(t)
        t.start()
        time.sleep(ramp_delay)

    def summarize():
        counts = {"connecting": 0, "login_ok": 0, "connected": 0, "failed": 0, "disconnected": 0, "idle": 0}
        for c in clients:
            counts[c.status] = counts.get(c.status, 0) + 1
        total = len(clients)
        print(f"[swarm] total={total} spawnados={counts['connected']} "
              f"logados(carregando)={counts['login_ok']} conectando={counts['connecting']} "
              f"falharam={counts['failed']} caíram={counts['disconnected']}")
        return counts

    start = time.time()
    try:
        while hold_seconds is None or (time.time() - start) < hold_seconds:
            time.sleep(3)
            summarize()
    except KeyboardInterrupt:
        pass

    print("[swarm] encerrando todos os bots...")
    for c in clients:
        c.running = False
    time.sleep(1)

    counts = summarize()

    errors = {}
    for c in clients:
        if c.status == "failed" and c.error:
            errors[c.error] = errors.get(c.error, 0) + 1
    if errors:
        print("[swarm] motivos de falha mais comuns:")
        for msg, n in sorted(errors.items(), key=lambda kv: -kv[1])[:10]:
            print(f"  ({n}x) {msg}")

    disc_reasons = {}
    for c in clients:
        if c.status == "disconnected" and c.disconnect_reason:
            disc_reasons[c.disconnect_reason] = disc_reasons.get(c.disconnect_reason, 0) + 1
    if disc_reasons:
        print("[swarm] motivos de desconexão mais comuns:")
        for msg, n in sorted(disc_reasons.items(), key=lambda kv: -kv[1])[:10]:
            print(f"  ({n}x) {msg}")

    return counts


def main():
    args = sys.argv[1:]
    debug = False
    if "--debug" in args:
        debug = True
        args.remove("--debug")

    move = False
    if "--move" in args:
        move = True
        args.remove("--move")

    spawn = None
    if "--spawn" in args:
        sidx = args.index("--spawn")
        try:
            sx, sy, sz = (float(v) for v in args[sidx + 1].split(","))
            spawn = (sx, sy, sz)
        except (IndexError, ValueError):
            print("Uso de --spawn: --spawn X,Y,Z (ex: --spawn 128.5,63,128.5)")
            sys.exit(1)
        del args[sidx:sidx + 2]

    source_ips = None
    if "--source-ips" in args:
        iidx = args.index("--source-ips")
        try:
            source_ips = parse_source_ips(args[iidx + 1])
        except (IndexError, ValueError):
            print("Uso de --source-ips: --source-ips 192.168.1.101-120  ou  ip1,ip2,ip3")
            sys.exit(1)
        del args[iidx:iidx + 2]
        if not source_ips:
            print("Uso de --source-ips: lista/faixa de IPs vazia ou inválida")
            sys.exit(1)

    usage = (f"Uso: {sys.argv[0]} [--debug] [--move] [--spawn X,Y,Z] [--source-ips ip1,ip2|ip.a-b] <host> <porta> <username>\n"
             f"     {sys.argv[0]} --swarm <quantidade> <host> <porta> [--prefix Bot] [--ramp 0.3] "
             f"[--hold segundos] [--move] [--spawn X,Y,Z] [--source-ips ip1,ip2|ip.a-b] [--debug]")

    if "--swarm" in args:
        idx = args.index("--swarm")
        try:
            count = int(args[idx + 1])
        except (IndexError, ValueError):
            print(usage)
            sys.exit(1)
        del args[idx:idx + 2]

        prefix = "Bot"
        if "--prefix" in args:
            pidx = args.index("--prefix")
            prefix = args[pidx + 1]
            del args[pidx:pidx + 2]

        ramp = 0.3
        if "--ramp" in args:
            ridx = args.index("--ramp")
            ramp = float(args[ridx + 1])
            del args[ridx:ridx + 2]

        hold = None
        if "--hold" in args:
            hidx = args.index("--hold")
            hold = float(args[hidx + 1])
            del args[hidx:hidx + 2]

        if len(args) != 2:
            print(usage)
            sys.exit(1)
        host, port = args[0], int(args[1])
        run_swarm(host, port, count, prefix=prefix, ramp_delay=ramp, debug=debug,
                  hold_seconds=hold, move=move, spawn=spawn, source_ips=source_ips)
        return

    if len(args) != 3:
        print(usage)
        sys.exit(1)

    host = args[0]
    port = int(args[1])
    username = args[2]

    client = PMClient(host, port, username, source_ip=(source_ips[0] if source_ips else None))
    client.debug = debug
    if spawn:
        client.spawn_x, client.spawn_y_foot, client.spawn_z = spawn
    try:
        client.connect_and_login(move=move)
    except Exception as e:
        print(f"[erro] {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
