# Scraper estandarizado EFICIENTE con sistema incremental
# source venv/bin/activate

import ssl
import certifi
ssl._create_default_https_context = lambda: ssl.create_default_context(cafile=certifi.where())

import requests
from bs4 import BeautifulSoup
import json
import time
import hashlib
from urllib.parse import urljoin, urlparse
import xml.etree.ElementTree as ET
import urllib.robotparser
import re
from datetime import datetime, timedelta
import os
from typing import Dict, Set, List, Tuple, Optional

# CONFIGURACIÓN GLOBAL
PRODUCCION = True  # Cambiar a True para scrapear sin límites
LIMITE_TEST = 999    # Límite de propiedades en modo test
E_COMPLETO = False  # False = incremental (novedades), True = completo (verificar cambios)

DATA_DIR = os.getenv('DATA_DIR', '.')
os.makedirs(DATA_DIR, exist_ok=True)

# Feed para WP All Import: SOLO propiedades disponibles (sin vendidas, reservadas ni eliminadas)
ARCHIVO_PROPIEDADES = os.getenv('ARCHIVO_PROPIEDADES', os.path.join(DATA_DIR, 'propiedades_menorca_estandarizado.json'))
# Histórico completo (incluye vendidas/reservadas/eliminadas). Es el estado del scraper entre ejecuciones.
ARCHIVO_HISTORICO   = os.getenv('ARCHIVO_HISTORICO',   os.path.join(DATA_DIR, 'propiedades_menorca_historico.json'))
ARCHIVO_REGISTRO    = os.getenv('ARCHIVO_REGISTRO',    os.path.join(DATA_DIR, 'registro_scraping.json'))
ARCHIVO_TEMP        = os.getenv('ARCHIVO_TEMP',        os.path.join(DATA_DIR, 'propiedades_temp.json'))

# En modo incremental, cada ficha ya conocida se vuelve a visitar como mucho cada N días
# para detectar si ha pasado a reservada/vendida o ha cambiado de precio.
DIAS_REVERIFICACION = int(os.getenv('DIAS_REVERIFICACION', '3'))

# Palabras que indican que la propiedad ya no está disponible (es, ca, en)
PATRON_NO_DISPONIBLE = re.compile(r'\b(VENDID[OA]S?|RESERVAD[OA]S?|VENUD[AE]S?|VENUTS?|RESERVAT(?:S|DA|DES)?|SOLD|RESERVED|UNDER OFFER)\b', re.IGNORECASE)


# Diccionario global para almacenar estados desde el listado
_estados_fincasseminari = {}
_estados_inmocampsbosch = {}



HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/115 Safari/537.36"
}

# Sesión HTTP compartida con reintentos: conexiones rechazadas, timeouts y servidores saturados
# (p.ej. Casas en Menorca a veces rechaza conexiones desde GitHub Actions)
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

SESSION = requests.Session()
_reintentos = Retry(
    total=3, connect=3, read=2, backoff_factor=3,
    status_forcelist=(429, 502, 503, 504), allowed_methods=frozenset(["GET"]),
    respect_retry_after_header=True, raise_on_status=False,
)
SESSION.mount("https://", HTTPAdapter(max_retries=_reintentos))
SESSION.mount("http://", HTTPAdapter(max_retries=_reintentos))

def detectar_flags(texto):
    """Detecta flags especiales en el texto"""
    if not texto:
        return dict(piscina=False, garaje=False, ascensor=False, vistas_mar=False, alquiler=False)
    t = texto.upper()
    return {
        'piscina': 'PISCINA' in t or 'POOL' in t,
        'garaje': 'GARAJE' in t or 'PARKING' in t or 'COCHERA' in t,
        'ascensor': 'ASCENSOR' in t,
        'vistas_mar': any(term in t for term in ['VISTAS AL MAR', 'VISTA AL MAR', 'FRENTE AL MAR', 'PRIMERA LINEA', 'SEA VIEWS']),
        'alquiler': 'ALQUILER' in t
    }

TIPOS_MAP = {
    'CHALET': 'Chalet',
    'ADOSADO': 'Chalet',
    'VILLA': 'Villa',
    'APARTAMENTO': 'Apartamento',
    'APTO': 'Apartamento',
    'CASA': 'Casa',
    'PISO': 'Piso',
    'PLANTA BAJA': 'Piso',
    'ÁTICO': 'Ático',
    'ATICO': 'Ático',
    'LOCAL': 'Local',
    'BAR': 'Local',
    'RESTAURANTE': 'Local',
    'DISCOTECA': 'Local',
    'PIZZERIA': 'Local',
    'SOLAR': 'Solar',
    'PARCELA': 'Solar',
    'EDIFICABLE': 'Solar',
    'GARAJE': 'Garaje',
    'PARKING': 'Garaje',
    'PARQUING': 'Garaje',
    'TERRENO': 'Terreno',
    'HUERTO': 'Huerto',
    'FINCA': 'Finca',
    'PREDIO': 'Finca',
    'CASA CAMPO': 'Finca',
    'NAVE': 'Nave',
    'OFICINA': 'Oficina',
    'VIVIENDA': 'Casa',
    'EDIFICIO SINGULAR': 'Edificio',
    'PALACIO': 'Edificio',
    'HOTEL': 'Edificio',
    'EDIFICIO': 'Edificio'
}

def detectar_tipo(texto):
    """Detecta tipo de propiedad en base al título u otro texto"""
    if not texto:
        return None
    upper = texto.upper()
    for key, value in TIPOS_MAP.items():
        if key in upper:
            return value
    return None

def estandarizar_ubicacion(ubicacion_raw):
    """
    Estandariza las ubicaciones según las reglas definidas
    """
    if not ubicacion_raw:
        return None
    
    mapeo_localidades = {
        'ciutadella de menorca': 'Ciutadella',
        'ciutadella': 'Ciutadella',
        'ciudadela': 'Ciutadella',
        'mahon': 'Maó',
        'mahón': 'Maó',
        'mao': 'Maó',
        'camí de maó': 'Ciutadella',
        'maó/mahón': 'Maó',
        'llumesanes': 'Maó; Llumesanes',
        'san clemente': 'Maó; Sant Climent',
        'san antonio': 'Maó; Port',
        'mahon puerto': 'Maó; Port',
        'cala llonga': 'Maó; Cala Llonga',
        'jardíns de malbuger': 'Maó',
        'es grau': 'Maó; Es grau',
        'ferrerias': 'Ferreries',
        'alayor': 'Alaior',
        'camí d\'en kane': 'Alaior',
        'son vilar': 'Maó',
        'son vilar con licencia turística': 'Maó',
        'son parc': 'Es Mercadal; Son Parc',
        'biniparratx': 'Sant Lluís',
        'san luis': 'Sant Lluís',
        'addaya': 'Es Mercadal; Addaia',
        'coves noves': 'Es Mercadal; Coves noves',
        'arenal': 'Es Mercadal; Arenal',
        'arenal d’en castell': 'Es Mercadal; Arenal',
        'arenal d\'en castell': 'Es Mercadal; Arenal',
        'punta prima': 'Sant Lluís; Punta Prima',
        'biniancolla': 'Maó; Biniancolla',
        'binisafua': 'Sant Lluís',
        'suestra': 'Sant Lluís',
        'son ganxo | son remei': 'Sant Lluís',
        'torret': 'Sant Lluís',
        'alcaufar': 'Sant Lluís',
        'cap den font': 'Sant Lluís',
        'salgar': 'Sant Lluís; Salgar',
        'binibeca': 'Sant Lluís; Binibeca',
        'binibeca vell': 'Sant Lluís; Binibeca',
        'l\'argentina': 'Alaior',
        'cala morell': 'Ciutadella; Cala Morell',
        'los delfines': 'Ciutadella; Cala\'n Blanes',
        'dalt es penyals': 'Ciutadella',
        'sa caleta': 'Ciutadella; Sa caleta',
        'cala\'n bosch': 'Ciutadella; Cap d\'Artrutx',
        'cap d\'artrutx': 'Ciutadella; Cap d\'Artrutx',
        'cap d\'artruix': 'Ciutadella; Cap d\'Artrutx',
        'cala blanca': 'Ciutadella; Cala Blanca',
        'cala blanca con licencia turística': 'Ciutadella; Cala Blanca',
        'son bou': 'Alaior; Son Bou',
        'cala\'n porter': 'Alaior; Cala en Porter',
        'cala en porter': 'Alaior; Cala en Porter',
        'binisafuller': 'Sant Lluís; Binisafuller',
        'binisafua roters': 'Sant Lluís; Binisafua',
        'binisafua rotters': 'Sant Lluís; Binisafua',
        'fornells': 'Es Mercadal; Fornells',
        'sant lluís': 'Sant Lluís',
        'sant lluis': 'Sant Lluís',
        'es castell': 'Es Castell',
        'villacarlos': 'Es Castell',
        'es migjorn gran': 'Es Migjorn Gran',
        'es migjorn': 'Es Migjorn Gran',
        'sant climent': 'Maó; Sant Climent',
    }
    
    terminos_eliminar = {
        'centro',
        'casco antiguo',
        'zonas rurales',
        'de menorca'
    }
    
    partes = []
    for separador in [';', ',']:
        if separador in ubicacion_raw:
            partes = [parte.strip() for parte in ubicacion_raw.split(separador)]
            break
    
    if not partes:
        partes = [ubicacion_raw.strip()]
    
    ubicacion_estandarizada = []
    for i, parte in enumerate(partes):
        parte_lower = parte.lower().strip()
        if i == 0:
            localidad_estandarizada = mapeo_localidades.get(parte_lower, parte.title())
            ubicacion_estandarizada.append(localidad_estandarizada)
        else:
            if parte_lower not in terminos_eliminar and parte.strip():
                localidad_estandarizada = mapeo_localidades.get(parte_lower, parte.title())
                ubicacion_estandarizada.append(localidad_estandarizada)
    
    resultado = []
    for item in ubicacion_estandarizada:
        if item not in resultado:
            resultado.append(item)
    
    return '; '.join(resultado) if len(resultado) > 1 else resultado[0] if resultado else None

def texto_indica_no_disponible(texto):
    """True si el texto (estado, etiqueta, título...) indica vendido o reservado"""
    return bool(texto and PATRON_NO_DISPONIBLE.search(str(texto)))

def esta_disponible(prop):
    """Una propiedad va al feed de WordPress solo si no está vendida, reservada ni eliminada"""
    if prop.get('vendido'):
        return False
    if prop.get('estado') == 'ELIMINADO_WEB':
        return False
    return not (texto_indica_no_disponible(prop.get('estado')) or texto_indica_no_disponible(prop.get('titulo')))

def limpiar_texto(txt):
    if not txt:
        return None
    # Quitar "Ref:" o "Ref." al inicio
    txt = re.sub(r'^\s*Ref[:\.]?\s*\d+\s*', '', txt, flags=re.IGNORECASE)
    # Quitar emojis y símbolos raros
    txt = re.sub(r'[^\w\sÁÉÍÓÚÜÑáéíóúüñ.,;:-]', '', txt)
    # Quitar asteriscos repetidos
    txt = re.sub(r'\*+', '', txt)
    # Normalizar espacios
    txt = re.sub(r'\s{2,}', ' ', txt).strip()
    return txt


class RegistroScraping:
    """Maneja el registro de URLs escaneadas y sus hashes mejorados"""
    
    def __init__(self, archivo_registro: str):
        self.archivo_registro = archivo_registro
        self.registro = self._cargar_registro()
    
    def _cargar_registro(self) -> Dict:
        """Carga el registro existente o crea uno nuevo"""
        if os.path.exists(self.archivo_registro):
            try:
                with open(self.archivo_registro, 'r', encoding='utf-8') as f:
                    return json.load(f)
            except Exception as e:
                print(f"Error cargando registro: {e}. Creando nuevo registro.")
        
        return {
            'urls_escaneadas': {},  # {url: {'hash_contenido': str, 'fecha_ultimo_escaneo': str}}
            'urls_eliminadas': {},  # {url: {'fecha_eliminacion': str, 'ultima_referencia': str}}
            'ultima_ejecucion_completa': None,
            'estadisticas': {
                'total_urls_conocidas': 0,
                'ultimo_escaneo_incremental': None,
                'cambios_detectados': 0,
                'urls_eliminadas': 0
            }
        }
    
    def guardar_registro(self):
        """Guarda el registro en disco"""
        try:
            with open(self.archivo_registro, 'w', encoding='utf-8') as f:
                json.dump(self.registro, f, ensure_ascii=False, indent=2)
        except Exception as e:
            print(f"Error guardando registro: {e}")
    
    def calcular_hash_contenido(self, precio: Optional[int], estado: Optional[str]) -> str:
        """Calcula hash MD5 del precio Y estado para detectar cambios importantes"""
        precio_str = str(precio) if precio is not None else "None"
        estado_str = str(estado) if estado is not None else "None"
        contenido = f"{precio_str}|{estado_str}"
        return hashlib.md5(contenido.encode()).hexdigest()[:8]
    
    def url_necesita_escaneo(self, url: str, precio: Optional[int], estado: Optional[str]) -> bool:
        """Determina si una URL necesita ser escaneada"""
        if E_COMPLETO:
            return True  # En modo completo, escanear todas
        
        if url not in self.registro['urls_escaneadas']:
            return True  # URL nueva, siempre escanear
        
        # En modo incremental, solo escanear si cambió el precio O el estado
        hash_actual = self.calcular_hash_contenido(precio, estado)
        hash_anterior = self.registro['urls_escaneadas'][url].get('hash_contenido', '')
        
        return hash_actual != hash_anterior
    
    def registrar_url_escaneada(self, url: str, precio: Optional[int], estado: Optional[str]):
        """Registra una URL como escaneada con su hash de contenido"""
        hash_contenido = self.calcular_hash_contenido(precio, estado)
        self.registro['urls_escaneadas'][url] = {
            'hash_contenido': hash_contenido,
            'fecha_ultimo_escaneo': datetime.now().isoformat()
        }
        
        # Si estaba marcada como eliminada, quitarla de ahí
        if url in self.registro['urls_eliminadas']:
            del self.registro['urls_eliminadas'][url]
        
        self.registro['estadisticas']['total_urls_conocidas'] = len(self.registro['urls_escaneadas'])
    
    def obtener_urls_conocidas(self) -> Set[str]:
        """Retorna el conjunto de URLs ya conocidas"""
        return set(self.registro['urls_escaneadas'].keys())

    def urls_para_reverificar(self, urls: List[str]) -> List[str]:
        """
        De las URLs dadas, devuelve las que toca volver a visitar en esta ejecución.
        Se reparten en DIAS_REVERIFICACION ejecuciones (las más antiguas primero), para que
        cada ficha se compruebe cada ~N días sin disparar el tiempo de ejecución.
        """
        if not urls or DIAS_REVERIFICACION <= 0:
            return []
        limite = datetime.now() - timedelta(days=DIAS_REVERIFICACION)
        escaneadas = self.registro['urls_escaneadas']

        def fecha(url):
            try:
                return datetime.fromisoformat(escaneadas[url]['fecha_ultimo_escaneo'])
            except (KeyError, TypeError, ValueError):
                return datetime.min

        caducadas = sorted((u for u in urls if fecha(u) < limite), key=fecha)
        cupo = -(-len(urls) // DIAS_REVERIFICACION)  # división redondeando hacia arriba
        return caducadas[:cupo]
    
    def marcar_ejecucion_completa(self):
        """Marca que se ejecutó un escaneo completo"""
        self.registro['ultima_ejecucion_completa'] = datetime.now().isoformat()

    def marcar_urls_eliminadas(self, urls_eliminadas: Set[str]) -> int:
        """Marca como eliminadas EXACTAMENTE las URLs recibidas (ya filtradas por inmobiliaria)."""
        eliminadas_count = 0
        for url in urls_eliminadas:
            if url not in self.registro['urls_eliminadas']:
                # Si quieres, aquí puedes rellenar 'ultima_referencia' si la guardas en otro lado
                self.registro['urls_eliminadas'][url] = {
                    'fecha_eliminacion': datetime.now().isoformat(),
                    'ultima_referencia': "desconocida"
                }
                eliminadas_count += 1

            # Quitar del pool de conocidas activas si estaba
            if url in self.registro['urls_escaneadas']:
                del self.registro['urls_escaneadas'][url]

        if eliminadas_count > 0:
            self.registro['estadisticas']['urls_eliminadas'] += eliminadas_count
            print(f"  🗑️ {eliminadas_count} URLs marcadas como eliminadas")

        return eliminadas_count

    
    def actualizar_estadisticas(self, cambios_detectados: int = 0):
        """Actualiza las estadísticas del registro"""
        if not E_COMPLETO:
            self.registro['estadisticas']['ultimo_escaneo_incremental'] = datetime.now().isoformat()
        self.registro['estadisticas']['cambios_detectados'] += cambios_detectados

class GestorPropiedades:
    """Maneja la carga, actualización y guardado de propiedades con preservación de fechas"""
    
    def __init__(self, archivo_propiedades: str, archivo_temp: str, archivo_historico: str):
        self.archivo_propiedades = archivo_propiedades
        self.archivo_historico = archivo_historico
        self.archivo_temp = archivo_temp
        self.propiedades_actuales = self._cargar_propiedades()
        self.propiedades_procesadas = []
        self.propiedades_por_inmobiliaria = {}  # Nuevo: organizar por inmobiliaria

    def _cargar_propiedades(self) -> List[Dict]:
        """Carga propiedades existentes desde el histórico (o desde el feed antiguo la primera vez)"""
        origen = self.archivo_historico if os.path.exists(self.archivo_historico) else self.archivo_propiedades
        if os.path.exists(origen):
            try:
                with open(origen, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                    # Si es el formato antiguo (lista), convertir al nuevo formato
                    if isinstance(data, list):
                        return data
                    # Si es el nuevo formato (dict por inmobiliaria), aplanar
                    elif isinstance(data, dict):
                        propiedades = []
                        for inmobiliaria, props in data.items():
                            if isinstance(props, list):
                                propiedades.extend(props)
                        return propiedades
            except Exception as e:
                print(f"Error cargando propiedades existentes: {e}")
        return []
    
    def obtener_urls_existentes(self) -> Dict[str, Dict]:
        """Retorna un diccionario {url: propiedad} de propiedades existentes"""
        return {prop['url_detalle']: prop for prop in self.propiedades_actuales}
    
    def agregar_propiedad(self, propiedad: Dict):
        """Agrega una nueva propiedad al buffer y organiza por inmobiliaria"""
        inmobiliaria = propiedad.get('inmobiliaria', 'Desconocida')
        
        if inmobiliaria not in self.propiedades_por_inmobiliaria:
            self.propiedades_por_inmobiliaria[inmobiliaria] = []
        
        self.propiedades_por_inmobiliaria[inmobiliaria].append(propiedad)
        self.propiedades_procesadas.append(propiedad)
        
        # Guardar progreso cada 10 propiedades
        if len(self.propiedades_procesadas) % 10 == 0:
            self._guardar_progreso()

    def _guardar_progreso(self):
        """Guarda el progreso actual en archivo temporal"""
        try:
            todas_propiedades = self.propiedades_actuales + self.propiedades_procesadas
            with open(self.archivo_temp, 'w', encoding='utf-8') as f:
                json.dump(todas_propiedades, f, ensure_ascii=False, indent=2)
            print(f"💾 Progreso guardado: {len(todas_propiedades)} propiedades")
        except Exception as e:
            print(f"⚠️ Error guardando progreso: {e}")

    
    def actualizar_propiedad_existente(self, url: str, nueva_propiedad: Dict) -> bool:
        """Actualiza una propiedad existente preservando la fecha_scraping original"""
        for i, prop in enumerate(self.propiedades_actuales):
            if prop['url_detalle'] == url:
                # Calcular hashes para detectar cambios
                hash_anterior = self._calcular_hash_propiedad(prop)
                hash_nuevo = self._calcular_hash_propiedad(nueva_propiedad)
                
                if hash_anterior != hash_nuevo:
                    # PRESERVAR fecha_scraping original
                    fecha_original = prop.get('fecha_scraping')
                    nueva_propiedad['fecha_scraping'] = fecha_original
                    nueva_propiedad['fecha_ultima_actualizacion'] = datetime.now().isoformat()
                    
                    self.propiedades_actuales[i] = nueva_propiedad
                    print(f"  🔄 Actualizada propiedad {nueva_propiedad.get('referencia', 'S/N')} - Contenido cambió")
                    return True
                else:
                    print(f"  ⭐️ Sin cambios en {nueva_propiedad.get('referencia', 'S/N')}")
                    return False
        return False
    
    def _calcular_hash_propiedad(self, propiedad: Dict) -> str:
        """Calcula hash de los campos relevantes (precio, estado, disponibilidad y datos básicos)"""
        campos = ('precio', 'estado', 'vendido', 'titulo', 'ubicacion', 'metros', 'metros_parcela', 'habitaciones', 'banos')
        contenido = "|".join(str(propiedad.get(c)) for c in campos)
        return hashlib.md5(contenido.encode()).hexdigest()[:8]
    
    def marcar_propiedades_eliminadas(self, urls_eliminadas: Set[str]) -> int:
        """Marca propiedades como vendidas si sus URLs fueron eliminadas"""
        eliminadas_count = 0
        for i, prop in enumerate(self.propiedades_actuales):
            if prop['url_detalle'] in urls_eliminadas and not prop.get('vendido', False):
                self.propiedades_actuales[i]['vendido'] = True
                self.propiedades_actuales[i]['estado'] = 'ELIMINADO_WEB'
                self.propiedades_actuales[i]['fecha_eliminacion'] = datetime.now().isoformat()
                eliminadas_count += 1
                print(f"  🗑️ Marcada como eliminada: {prop.get('referencia', 'S/N')}")
        
        return eliminadas_count
    
    def finalizar_y_guardar(self, guardar_por_inmobiliaria: bool = False):
        """Finaliza el proceso y guarda el archivo definitivo"""
        todas_propiedades = self.propiedades_actuales + self.propiedades_procesadas

        # Eliminar duplicados por URL: los datos más recientes (los últimos de la lista) mandan,
        # pero se conserva la fecha_scraping más antigua (primera vez que se encontró)
        propiedades_unicas = {}
        for prop in todas_propiedades:
            url = prop['url_detalle']
            anterior = propiedades_unicas.get(url)
            if anterior is None:
                propiedades_unicas[url] = prop
                continue
            nueva = prop.copy()
            fechas = [f for f in (anterior.get('fecha_scraping'), prop.get('fecha_scraping')) if f]
            nueva['fecha_scraping'] = min(fechas) if fechas else None
            if self._calcular_hash_propiedad(anterior) != self._calcular_hash_propiedad(prop):
                nueva['fecha_ultima_actualizacion'] = datetime.now().isoformat()
            else:
                nueva['fecha_ultima_actualizacion'] = anterior.get('fecha_ultima_actualizacion')
            propiedades_unicas[url] = nueva

        resultado_final = list(propiedades_unicas.values())
        for prop in resultado_final:
            # Restos de ubicaciones mal leídas (referencias como "7117" o "089") en datos antiguos
            if re.fullmatch(r'[\d\s()]+', str(prop.get('ubicacion') or '')):
                prop['ubicacion'] = None
        disponibles = [p for p in resultado_final if esta_disponible(p)]

        try:
            # Histórico completo: estado del scraper para la próxima ejecución
            with open(self.archivo_historico, 'w', encoding='utf-8') as f:
                json.dump(resultado_final, f, ensure_ascii=False, indent=2)

            if guardar_por_inmobiliaria:
                # Organizar por inmobiliaria
                propiedades_organizadas = {}
                for prop in disponibles:
                    inmobiliaria = prop.get('inmobiliaria', 'Desconocida')
                    if inmobiliaria not in propiedades_organizadas:
                        propiedades_organizadas[inmobiliaria] = []
                    propiedades_organizadas[inmobiliaria].append(prop)

                # Guardar en formato organizado
                with open(self.archivo_propiedades, 'w', encoding='utf-8') as f:
                    json.dump(propiedades_organizadas, f, ensure_ascii=False, indent=2)
            else:
                # Feed para WordPress: solo disponibles, en formato plano (lista)
                with open(self.archivo_propiedades, 'w', encoding='utf-8') as f:
                    json.dump(disponibles, f, ensure_ascii=False, indent=2)

            # Limpiar archivo temporal
            if os.path.exists(self.archivo_temp):
                os.remove(self.archivo_temp)

            print(f"🗂️ Histórico: {len(resultado_final)} propiedades | Feed WordPress (disponibles): {len(disponibles)}")
            return len(disponibles)
        except Exception as e:
            print(f"Error guardando archivo final: {e}")
            return 0


def crear_propiedad_estandar(**kwargs):
    """Crea una propiedad con estructura estandarizada mejorada"""

    precio = kwargs.get('precio', None)
    alquiler = kwargs.get('alquiler', False)

    # Cualquier estado/título que indique vendido o reservado marca la propiedad como no disponible
    vendido = bool(kwargs.get('vendido', False)) or texto_indica_no_disponible(kwargs.get('estado')) \
        or texto_indica_no_disponible(kwargs.get('titulo'))

    # 🔽 Nueva validación: si es alquiler y el precio supera 6000€, marcar como False
    if alquiler and (not precio or precio == 0 or precio > 10000):
        alquiler = False


    return {
        "referencia": kwargs.get('referencia', ''),
        "titulo": kwargs.get('titulo', ''),
        "ubicacion": kwargs.get('ubicacion', ''),
        "precio": kwargs.get('precio', None),
        "metros": kwargs.get('metros', None),
        "metros_parcela": kwargs.get('metros_parcela', None),
        "habitaciones": kwargs.get('habitaciones', None),
        "banos": kwargs.get('banos', None),
        "tipo": kwargs.get('tipo', ''),
        "estado": kwargs.get('estado', ''),
        "piscina": kwargs.get('piscina', False),
        "garaje": kwargs.get('garaje', False),
        "ascensor": kwargs.get('ascensor', False),
        "vistas_mar": kwargs.get('vistas_mar', False),
        "vendido": vendido,
        "alquiler": alquiler,
        "url_detalle": kwargs.get('url_detalle', ''),
        "inmobiliaria": kwargs.get('inmobiliaria', ''),
        "imagen_destacada": kwargs.get('imagen_destacada', ''),
        "galeria": kwargs.get('galeria', []),
        "fecha_scraping": kwargs.get('fecha_scraping', datetime.now().isoformat()),  # Permitir override
        "fecha_ultima_actualizacion": kwargs.get('fecha_ultima_actualizacion', None)  # Nueva para tracking
    }

_robots_cache = {}

def is_allowed(url):
    """Verifica si el scraping está permitido por robots.txt (se descarga una vez por dominio)"""
    parsed = urlparse(url)
    base = f"{parsed.scheme}://{parsed.netloc}"
    if base not in _robots_cache:
        robots_url = urljoin(base, "/robots.txt")
        rp = urllib.robotparser.RobotFileParser(robots_url)
        try:
            # Se descarga con nuestros HEADERS: algunas webs (p.ej. Lucas Fox) dan 403 al User-Agent de urllib
            r = SESSION.get(robots_url, headers=HEADERS, timeout=15)
            if r.status_code in (401, 403):
                rp.disallow_all = True
            elif r.status_code >= 400:
                rp.allow_all = True
            else:
                rp.parse(r.text.splitlines())
        except:
            print(f"No se pudo acceder a {robots_url}")
            rp = None
        _robots_cache[base] = rp
    rp = _robots_cache[base]
    return rp.can_fetch(HEADERS['User-Agent'], url) if rp else True

def scraper_eficiente_website(scraper_func, nombre_inmobiliaria: str, 
                             registro: RegistroScraping, 
                             gestor: GestorPropiedades, 
                             obtener_urls_func, *args):
    """
    Wrapper genérico para scrapers que implementa la lógica eficiente
    """
    print(f"🏠 Iniciando scraping {'COMPLETO' if E_COMPLETO else 'INCREMENTAL'} de {nombre_inmobiliaria}...")
    
    # Obtener URLs disponibles
    if args:
        urls_disponibles = obtener_urls_func(*args)
    else:
        urls_disponibles = obtener_urls_func()
    
    if not urls_disponibles:
        print(f"No se encontraron URLs de propiedades en {nombre_inmobiliaria}")
        return []
    
    # Convertir a conjunto de URLs para facilitar comparaciones
    urls_encontradas = {url for _, url in urls_disponibles}
    urls_conocidas = registro.obtener_urls_conocidas()
    propiedades_existentes = gestor.obtener_urls_existentes()
    
    # DETECTAR URLs ELIMINADAS
    urls_eliminadas_inmobiliaria = {url for url in urls_conocidas 
                                   if url not in urls_encontradas 
                                   and any(prop.get('inmobiliaria') == nombre_inmobiliaria 
                                          for prop in gestor.propiedades_actuales 
                                          if prop['url_detalle'] == url)}
    
    if urls_eliminadas_inmobiliaria:
        eliminadas_count = registro.marcar_urls_eliminadas(urls_eliminadas_inmobiliaria)
        gestor.marcar_propiedades_eliminadas(urls_eliminadas_inmobiliaria)
        print(f"  🗑️ {len(urls_eliminadas_inmobiliaria)} URLs eliminadas detectadas en {nombre_inmobiliaria}")
    
    urls_a_procesar = []
    urls_nuevas = 0
    urls_omitidas = 0

    # En incremental, las fichas ya guardadas se re-verifican por turnos (reservadas, vendidas, cambios de precio)
    urls_reverificar = set() if E_COMPLETO else set(registro.urls_para_reverificar(
        [url for _, url in urls_disponibles if url in propiedades_existentes]))

    # Filtrar URLs según el modo
    for referencia, url in urls_disponibles:
        reaparecida = url in propiedades_existentes and (
            url not in urls_conocidas or propiedades_existentes[url].get('estado') == 'ELIMINADO_WEB')
        if E_COMPLETO or url not in propiedades_existentes or reaparecida:
            # Nueva, o reaparecida en la web tras marcarse como eliminada
            urls_a_procesar.append((referencia, url))
            if url not in propiedades_existentes:
                urls_nuevas += 1
        elif url in urls_reverificar:
            urls_a_procesar.append((referencia, url))
        else:
            urls_omitidas += 1

    urls_conocidas_inmo = {
        u for u in urls_conocidas
        if any(prop.get('inmobiliaria') == nombre_inmobiliaria
               for prop in gestor.propiedades_actuales
               if prop['url_detalle'] == u)
    }
    
    print(f"  📊 URLs encontradas: {len(urls_disponibles)}")
    print(f"  📊 URLs conocidas ({nombre_inmobiliaria}): {len(urls_conocidas_inmo)}")
    print(f"  📊 URLs nuevas: {urls_nuevas}")
    print(f"  📊 URLs a re-verificar: {len(urls_reverificar)}")
    print(f"  📊 URLs a procesar: {len(urls_a_procesar)}")
    print(f"  📊 URLs omitidas (sin cambios): {urls_omitidas}")
    
    if not urls_a_procesar:
        print(f"  ✅ No hay URLs nuevas que procesar en {nombre_inmobiliaria}")
        return []
    
    # Aplicar límite si estamos en modo test
    if not PRODUCCION:
        urls_a_procesar = urls_a_procesar[:LIMITE_TEST]
        print(f"  ⚠️  Limitando a {len(urls_a_procesar)} URLs (modo test)")
    
    propiedades_procesadas = []
    cambios_detectados = 0
    
    for i, (referencia, url) in enumerate(urls_a_procesar, 1):
        print(f"  Procesando {i}/{len(urls_a_procesar)}: REF.{referencia}")
        
        if not is_allowed(url):
            print(f"    🚫 Bloqueado por robots.txt")
            continue
        
        try:
            # Scraper específico
            data = scraper_func(url, referencia)
            if data:
                if url in propiedades_existentes:
                    # Ya existía (modo completo o re-verificación): verificar cambios preservando fecha original
                    prop_existente = propiedades_existentes[url]
                    data['fecha_scraping'] = prop_existente.get('fecha_scraping', data['fecha_scraping'])
                    
                    if gestor.actualizar_propiedad_existente(url, data):
                        cambios_detectados += 1
                else:
                    # Modo incremental: agregar nueva propiedad
                    gestor.agregar_propiedad(data)
                    propiedades_procesadas.append(data)
                
                # Registrar URL como escaneada
                registro.registrar_url_escaneada(url, data.get('precio'), data.get('estado'))
                
                # Guardar registro cada 20 propiedades
                if i % 20 == 0:
                    registro.guardar_registro()
        
        except Exception as e:
            print(f"    ❌ Error procesando {url}: {e}")
        
        time.sleep(1)  # Pausa respetuosa
    
    # Actualizar estadísticas
    registro.actualizar_estadisticas(cambios_detectados)
    registro.guardar_registro()
    
    resultado_count = len(propiedades_procesadas) + cambios_detectados
    print(f"  ✅ {nombre_inmobiliaria}: {len(propiedades_procesadas)} nuevas, {cambios_detectados} actualizadas")
    
    return propiedades_procesadas

# Ejemplo de integración con un scraper existente (usando Fincas Llongas como ejemplo)
def obtener_urls_sitemap_principal(sitemap_url, filtro_subsitemap=None):
    """Obtener sub-sitemaps relevantes"""
    try:
        resp = SESSION.get(sitemap_url, headers=HEADERS)
        resp.raise_for_status()
        root = ET.fromstring(resp.content)
        urls = []

        if filtro_subsitemap:
            sitemap_tags = root.findall(".//{http://www.sitemaps.org/schemas/sitemap/0.9}sitemap")
            for sitemap in sitemap_tags:
                loc = sitemap.find("{http://www.sitemaps.org/schemas/sitemap/0.9}loc")
                if loc is not None and filtro_subsitemap in loc.text:
                    urls.append(loc.text)
        else:
            urls.append(sitemap_url)
        
        return urls
    except Exception as e:
        print(f"Error al obtener sitemap principal {sitemap_url}: {e}")
        return []

def obtener_urls_pisos_de_subsitemap(subsitemap_url, patrones_validos, max_urls=None):
    """Obtener URLs de propiedades según patrón configurado, filtrando por últimos 2 años"""
    try:
        resp = SESSION.get(subsitemap_url, headers=HEADERS)
        resp.raise_for_status()
        root = ET.fromstring(resp.content)
        urls = []
        
        # Calcular fecha límite (hoy - 2 años)
        fecha_limite = datetime.now() - timedelta(days=2*365)
        
        url_tags = root.findall(".//{http://www.sitemaps.org/schemas/sitemap/0.9}url")
        for url_tag in url_tags:
            loc = url_tag.find("{http://www.sitemaps.org/schemas/sitemap/0.9}loc")
            lastmod = url_tag.find("{http://www.sitemaps.org/schemas/sitemap/0.9}lastmod")
            
            # Verificar fecha de modificación
            fecha_valida = True
            if lastmod is not None and lastmod.text:
                try:
                    fecha_mod = datetime.strptime(lastmod.text, "%Y-%m-%dT%H:%M:%S%z")
                    if fecha_mod.replace(tzinfo=None) < fecha_limite:
                        fecha_valida = False
                except ValueError:
                    # Si hay error en el formato de fecha, asumir que es válida
                    pass
            
            if (fecha_valida and loc is not None and 
                any(pat in loc.text for pat in patrones_validos)):
                parsed_url = urlparse(loc.text)
                path = parsed_url.path
                if (not path.startswith(("/ca/", "/en/", "/fr/"))
                    and "mallorca" not in loc.text.lower()):
                    urls.append(loc.text)
                    if max_urls and len(urls) >= max_urls:
                        break
        return urls
    except Exception as e:
        print(f"Error al obtener sitemap de pisos {subsitemap_url}: {e}")
        return []

def obtener_urls_fincasllongas():
    """Función para obtener URLs de Fincas Llongas"""
    domain = 'fincasllongas.com'
    base_url = f"https://{domain}"
    sitemap_url = urljoin(base_url, '/sitemap.xml')
    
    subsitemaps = obtener_urls_sitemap_principal(sitemap_url, 'realestate')
    
    if not subsitemaps:
        print(f"No se encontraron sitemaps válidos en {sitemap_url}")
        return []
    
    all_property_urls = []
    patrones_validos = ['/propiedad/']
    
    for subsitemap in subsitemaps:
        property_urls = obtener_urls_pisos_de_subsitemap(subsitemap, patrones_validos, None)
        all_property_urls.extend(property_urls)
    
    # Convertir URLs a tuplas (referencia, url)
    urls_con_ref = []
    for url in all_property_urls:
        # Extraer referencia de la URL o usar un identificador
        ref_match = re.search(r'/(\d+)/?$', url)
        if ref_match:
            referencia = ref_match.group(1)
        else:
            # Usar parte de la URL como referencia
            referencia = url.split('/')[-2] if url.endswith('/') else url.split('/')[-1]
            referencia = referencia[:10]  # Limitar longitud
        urls_con_ref.append((referencia, url))
    
    return urls_con_ref

def scrape_fincasllongas_detalle(url, referencia):
    """Scraper específico para una propiedad de fincasllongas.com"""
    try:
        r = SESSION.get(url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, 'html.parser')
        
        # ===========================
        # REFERENCIA & UBICACIÓN
        # ===========================
        ubicacion = ''
        referencia = ''

        h2 = soup.find('h2')
        if h2:
            strong = h2.find('strong')
            if strong:
                referencia = strong.get_text(strip=True)  # "Ref. 7610"
                strong.extract()
            ubicacion = h2.get_text(strip=True)
            ubicacion = estandarizar_ubicacion(ubicacion)

        # ===========================
        # PRECIO
        # ===========================
        precio = None
        precio_tag = soup.select_one('.price')
        if precio_tag:
            precio_text = (
                precio_tag.text.strip()
                .replace('.', '')
                .replace('€', '')
                .replace('Precio', '')
                .strip()
            )
            precio_limpio = re.sub(r'[^\d]', '', precio_text)
            if precio_limpio.isdigit():
                precio = int(precio_limpio)

        # ===========================
        # TÍTULO
        # ===========================
        titulo = None
        hgroup_tag = soup.find('hgroup')
        if hgroup_tag:
            titulo_tag = hgroup_tag.find('h1')
            if titulo_tag:
                titulo = titulo_tag.text.strip()

        # ===========================
        # SUPERFICIE
        # ===========================
        metros_parcela = None   # 1ª superficie (ej. 5.700)
        metros = None           # 2ª superficie (ej. 120)

        max_data_items = soup.select('ul.data-main li.max-data')
        superficie_count = 0
        for li in max_data_items:
            em = li.find('em')
            strong = li.find('strong')
            if em and 'superficie' in em.text.lower() and strong and strong.text.strip() != '-':
                superficie_text = (
                    strong.get_text(strip=True)
                    .replace('Superficie', '')
                    .replace('m', '')
                    .strip()
                )
                if superficie_text.endswith(('2', '²')):
                    superficie_text = superficie_text[:-1]

                superficie_text = superficie_text.replace('.', '').replace(',', '').strip()
                try:
                    valor = int(superficie_text)
                except ValueError:
                    continue

                superficie_count += 1
                if superficie_count == 1:
                    metros_parcela = valor
                elif superficie_count == 2:
                    metros = valor
                    break

        # ===========================
        # HABITACIONES / BAÑOS
        # ===========================
        habitaciones = None
        banos = None
        data_main = soup.select('ul.data-main li')
        for li in data_main:
            em = li.find('em')
            strong = li.find('strong')
            if not em or not strong:
                continue
            key = em.text.strip().lower()
            val = strong.text.strip()
            if key == 'habitaciones' and val.isdigit():
                habitaciones = int(val)
            elif key == 'baños' and val.isdigit():
                banos = int(val)

        # ===========================
        # TIPO
        # ===========================
        tipo = detectar_tipo(titulo)

        # ===========================
        # ESTADO
        # ===========================
        vendido = bool(soup.select_one('.status-pro'))
        estado = 'VENDIDO' if vendido else None

        # ===========================
        # FLAGS (piscina, garaje, etc.)
        # ===========================
        cms_divs = soup.select("div.cms")
        texto_completo = " ".join(div.get_text(" ", strip=True) for div in cms_divs).upper()
        flags = detectar_flags(texto_completo)
        piscina, garaje, ascensor, vistas_mar, alquiler = (
            flags['piscina'], flags['garaje'], flags['ascensor'], flags['vistas_mar'], flags['alquiler']
        )

        alquiler = False

        # ===========================
        # GALERÍA DE IMÁGENES
        # ===========================
        galeria = []
        vistos = set()
        imagenes = soup.select('img.slide-1, .gallery img, .images img')
        for img in imagenes:
            if img.has_attr('src'):
                src = urljoin(url, img['src'])
                src_lower = src.lower()
                if not any(x in src_lower for x in ['logo', 'icon', 'banner']):
                    if src not in vistos:
                        galeria.append(src)
                        vistos.add(src)

        imagen_destacada = galeria[0] if galeria else ''

        # ===========================
        # CREAR PROPIEDAD
        # ===========================
        return crear_propiedad_estandar(
            referencia=referencia,
            titulo=titulo,
            ubicacion=ubicacion,
            precio=precio,
            metros=metros,
            metros_parcela=metros_parcela,
            habitaciones=habitaciones,
            banos=banos,
            tipo=tipo,
            estado=estado,
            piscina=piscina,
            garaje=garaje,
            ascensor=ascensor,
            vistas_mar=vistas_mar,
            vendido=vendido,
            alquiler=alquiler,
            url_detalle=url,
            inmobiliaria='Fincas Llongas',
            imagen_destacada=imagen_destacada,
            galeria=galeria
        )
    except Exception as e:
        print(f"Error scrapeando Fincas Llongas {url}: {e}")
        return None

def obtener_urls_artrutx():
    """Obtener todas las URLs de propiedades de Artrutx desde el listado con sus referencias"""
    url_listado = "https://www.inmobiliariaartrutx.com/venta.php"
    try:
        r = SESSION.get(url_listado, headers=HEADERS, timeout=30)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, 'html.parser')

        urls_propiedades = []
        productos = soup.find_all('div', class_='product-img')

        for producto in productos:
            enlace = producto.find('a', href=re.compile(r'detalles-propiedad\.php\?id_p=\d+'))
            referencia_elemento = producto.select_one('.product-img-gallery ul li')
            if enlace and referencia_elemento:
                href = enlace.get('href')
                referencia_texto = referencia_elemento.get_text(strip=True)
                referencia_match = re.search(r'REF\.(\d+)', referencia_texto)
                if referencia_match:
                    referencia = referencia_match.group(1)
                    url_completa = urljoin(url_listado, href) if not href.startswith('http') else href
                    urls_propiedades.append((referencia, url_completa))

        urls_unicas = list(set(urls_propiedades))
        return urls_unicas
    except Exception as e:
        print(f"Error obteniendo URLs de Artrutx: {e}")
        return []


def scrape_artrutx_detalle(url, referencia):
    """Scraper específico para una propiedad de inmobiliariaartrutx.com"""
    try:
        r = SESSION.get(url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, 'html.parser')
        for tag in soup(["header", "footer"]):
            tag.decompose()
        if (div_borrar := soup.find("div", id="ltn__utilize-mobile-menu")):
            div_borrar.decompose()

        # ===========================
        # TÍTULO
        # ===========================
        titulo = None
        h1 = soup.find('h1')
        if h1:
            t = h1.get_text(strip=True)
            titulo = t if len(t) > 4 else None
        if not titulo:
            texto = soup.get_text()
            lineas = [l.strip() for l in texto.split('\n') if l.strip()]
            for linea in lineas[:10]:
                if any(keyword in linea.upper() for keyword in [
                    'APARTAMENTO','CASA','CHALET','PISO','ÁTICO','LOCAL','HUERTO',
                    'SOLAR','GARAJE','TERRENO','NAVE'
                ]) and len(linea) > 5:
                    titulo = linea
                    break

        # ===========================
        # PRECIO
        # ===========================
        precio = None
        texto_completo = soup.get_text()
        for pattern in [r'(\d{1,3}(?:[.,]\d{3})*)\s*€', r'€\s*(\d{1,3}(?:[.,]\d{3})*)']:
            match = re.search(pattern, texto_completo)
            if match:
                precio_str = match.group(1).replace('.', '').replace(',', '')
                if precio_str.isdigit():
                    precio = int(precio_str)
                    break

        # ===========================
        # UBICACIÓN
        # ===========================
        ubicacion = None
        label = soup.select_one('label:has(i.flaticon-pin)')
        if label:
            text = label.get_text(" ", strip=True)
            partes = [re.sub(r"\s+", " ", re.sub(r"[´'`]", "'", p.strip())) for p in text.split(';')]
            ubicacion_list = []
            for p in partes:
                if p and p not in ubicacion_list:
                    ubicacion_list.append(p)
            ubicacion = '; '.join(ubicacion_list) if ubicacion_list else None
        ubicacion = estandarizar_ubicacion(ubicacion)

        # ===========================
        # CARACTERÍSTICAS
        # ===========================
        habitaciones = banos = metros = metros_parcela = None
        for item in soup.select('.property-detail-feature-list-item'):
            etiqueta = item.select_one('h6')
            valor = item.select_one('small')
            if not etiqueta or not valor:
                continue
            texto_etiqueta = etiqueta.get_text(strip=True).lower()
            texto_valor = ''.join(valor.stripped_strings).strip()
            if 'habitaciones' in texto_etiqueta and texto_valor.isdigit():
                habitaciones = int(texto_valor)
            elif 'baños' in texto_etiqueta and texto_valor.isdigit():
                banos = int(texto_valor)
            elif 'superficie' in texto_etiqueta:
                metros_str = texto_valor.replace('m²', '').replace('m', '').strip()
                if metros_str.endswith(('2','²')):
                    metros_str = metros_str[:-1].strip()
                if metros_str.isdigit():
                    metros = int(metros_str)
            elif 'parcela' in texto_etiqueta:
                parcela_str = texto_valor.replace('m²','').replace('m','').strip()
                if parcela_str.endswith(('2','²')):
                    parcela_str = parcela_str[:-1].strip()
                if parcela_str.isdigit():
                    metros_parcela = int(parcela_str)

        # ===========================
        # ESTADO
        # ===========================
        estado_tag = soup.select_one('.ltn__blog-meta li.ltn__blog-category a')
        estado = estado_tag.get_text(strip=True) if estado_tag else None
        vendido = False
        if estado:
            texto_upper = estado.upper()
            if 'VENDIDO' in texto_upper:
                vendido = True
                estado = 'VENDIDO'

        # ===========================
        # FLAGS
        # ===========================
        flags = detectar_flags(texto_completo.upper())
        piscina, garaje, ascensor, vistas_mar, alquiler = (
            flags['piscina'], flags['garaje'], flags['ascensor'], flags['vistas_mar'], flags['alquiler']
        )

        # ===========================
        # GALERÍA
        # ===========================
        galeria = []
        img_selectors = [
            'img[src*="propiedad"]','.gallery img','.images img',
            'img:not([src*="logo"]):not([src*="icon"]):not([src*="banner"])'
        ]
        for selector in img_selectors:
            imagenes = soup.select(selector)
            for img in imagenes:
                if img.has_attr('src'):
                    src = img['src']
                    if not any(x in src.lower() for x in ['logo','icon','banner','menu','wapp']):
                        imagen_url = urljoin(url, src)
                        if imagen_url not in galeria:
                            galeria.append(imagen_url)
        imagen_destacada = galeria[0] if galeria else ''

        # ===========================
        # CREAR PROPIEDAD
        # ===========================
        tipo = detectar_tipo(titulo)
        return crear_propiedad_estandar(
            referencia=referencia,
            titulo=titulo,
            ubicacion=ubicacion,
            precio=precio,
            metros=metros,
            metros_parcela=metros_parcela,
            habitaciones=habitaciones,
            banos=banos,
            tipo=tipo,
            estado=estado,
            piscina=piscina,
            garaje=garaje,
            ascensor=ascensor,
            vistas_mar=vistas_mar,
            vendido=vendido,
            alquiler=alquiler,
            url_detalle=url,
            inmobiliaria='Inmobiliaria Artrutx',
            imagen_destacada=imagen_destacada,
            galeria=galeria
        )
    except Exception as e:
        print(f"Error scrapeando Artrutx {url}: {e}")
        return None

def obtener_urls_fincasciutadella():
    """Obtener todas las URLs de propiedades de Fincas Ciutadella desde el listado con sus referencias"""
    url_listado = "https://www.fincasciutadella.com/propiedad-venta.php"
    try:
        r = SESSION.get(url_listado, headers=HEADERS, timeout=30)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, 'html.parser')

        urls_propiedades = []
        productos = soup.find_all('div', class_=lambda x: x and 'listing-grid-box' in x)

        for producto in productos:
            enlace = producto.find('a', href=re.compile(r'propiedad-v\.php\?id=\d+'))
            if not enlace:
                enlace = producto.find('a', href=re.compile(r'detalles.*\.php\?id.*=\d+'))

            referencia = None
            if enlace:
                texto_enlace = enlace.get_text()
                match = re.search(r'REF:\s*(\d+)', texto_enlace, re.IGNORECASE)
                if match:
                    referencia = match.group(1)

            if not referencia:
                h4 = producto.find('h4')
                if h4:
                    match = re.search(r'REF:\s*(\d+)', h4.get_text(), re.IGNORECASE)
                    if match:
                        referencia = match.group(1)

            if enlace and referencia:
                href = enlace.get('href')
                url_completa = href if href.startswith('http') else urljoin(url_listado, href)
                urls_propiedades.append((referencia, url_completa))

        return list(set(urls_propiedades))
    except Exception as e:
        print(f"Error obteniendo URLs de Fincas Ciutadella: {e}")
        return []


def scrape_fincasciutadella_detalle(url, referencia):
    """Scraper específico para una propiedad de fincasciutadella.com"""
    try:
        r = SESSION.get(url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, 'html.parser')
        for tag in soup(["header", "footer"]):
            tag.decompose()

        # ===========================
        # TÍTULO
        # ===========================
        titulo = None
        filas_detalle = soup.select('ul.rel-ls-none.p-addtional-box li')
        for fila in filas_detalle:
            cabecera = fila.select_one('.p-f-box-head')
            info = fila.select_one('.p-f-box-info')
            if cabecera and info:
                if 'PROPIEDAD' in cabecera.get_text(strip=True).upper():
                    raw = info.get_text(strip=True)
                    if ' - ' in raw:
                        titulo = raw.split(' - ', 1)[1].strip()
                    else:
                        titulo = raw
                    break

        if not titulo:
            h1 = soup.find('h1')
            if h1:
                titulo = h1.get_text(strip=True)

        # ===========================
        # PRECIO
        # ===========================
        precio = None
        precio_tag = soup.select_one('.grid-price, .price, .precio, .property-price')
        if precio_tag:
            precio_txt = precio_tag.get_text(strip=True)
            precio_limpio = re.sub(r'[^\d]', '', precio_txt)
            if precio_limpio.isdigit():
                precio = int(precio_limpio)

        if not precio:
            texto_completo = soup.get_text()
            match = re.search(r'(\d{1,3}(?:\.\d{3})*)\s*€', texto_completo)
            if match:
                precio = int(match.group(1).replace('.', ''))

        # ===========================
        # UBICACIÓN
        # ===========================
        ubicacion_parts = []
        for fila in filas_detalle:
            cabecera = fila.select_one('.p-f-box-head')
            info = fila.select_one('.p-f-box-info')
            if not cabecera or not info:
                continue
            txt = cabecera.get_text(strip=True).upper()
            val = info.get_text(strip=True)
            if 'LOCALIDAD' in txt:
                ubicacion_parts.append(val)
            elif 'ZONAS' in txt and val not in ubicacion_parts:
                ubicacion_parts.append(val)
        ubicacion = '; '.join(ubicacion_parts) if ubicacion_parts else None
        ubicacion = estandarizar_ubicacion(ubicacion)

        # ===========================
        # CARACTERÍSTICAS
        # ===========================
        habitaciones = banos = metros = metros_parcela = None
        piscina = garaje = ascensor = False

        for fila in filas_detalle:
            cabecera = fila.select_one('.p-f-box-head')
            info = fila.select_one('.p-f-box-info')
            if not cabecera or not info:
                continue
            txt = cabecera.get_text(strip=True).upper()
            val = info.get_text(strip=True).upper()

            if 'HABITACIONES' in txt and val.isdigit():
                habitaciones = int(val)
            elif 'BAÑOS' in txt and val.isdigit():
                banos = int(val)
            elif 'SUPERFICIE' in txt:
                m = re.search(r'(\d+)', val)
                if m and m.group(1) != '2':
                    metros = int(m.group(1))
            elif 'PARCELA' in txt:
                m = re.search(r'(\d+)', val)
                if m and m.group(1) != '2':
                    metros_parcela = int(m.group(1))
            elif 'PISCINA' in txt:
                piscina = 'SI' in val or 'SÍ' in val
            elif 'GARAJE' in txt:
                garaje = 'SI' in val or 'SÍ' in val
            elif 'ASCENSOR' in txt:
                ascensor = 'SI' in val or 'SÍ' in val

            alquiler = False

        # ===========================
        # ESTADO
        # ===========================
        estado = None
        vendido = False
        estado_elem = soup.select_one('.grid-status')
        if estado_elem:
            estado_txt = estado_elem.get_text(strip=True).upper()
            if 'VENDIDO' in estado_txt or 'SOLD' in estado_txt:
                estado, vendido = 'VENDIDO', True

        texto_completo = soup.get_text().upper()
        if 'VENDIDO' in texto_completo:
            estado, vendido = 'VENDIDO', True

        vistas_mar = any(t in texto_completo for t in ['VISTAS AL MAR','SEA VIEW','VISTA MAR'])

        # ===========================
        # GALERÍA
        # ===========================
        galeria = []
        vistos = set()
        img_selectors = [
            'img[src*="panel/inmuebles"]','img[src*="propiedad"]',
            '.gallery img','.images img','.property-images img'
        ]
        for selector in img_selectors:
            imagenes = soup.select(selector)
            for img in imagenes:
                if img.has_attr('src'):
                    src = urljoin(url, img['src'])
                    if not any(x in src.lower() for x in ['logo','icon','banner']) and src not in vistos:
                        galeria.append(src)
                        vistos.add(src)
        imagen_destacada = galeria[0] if galeria else ''

        # ===========================
        # CREAR PROPIEDAD
        # ===========================
        tipo = detectar_tipo(titulo)
        return crear_propiedad_estandar(
            referencia=referencia,
            titulo=titulo,
            ubicacion=ubicacion,
            precio=precio,
            metros=metros,
            metros_parcela=metros_parcela,
            habitaciones=habitaciones,
            banos=banos,
            tipo=tipo,
            estado=estado,
            piscina=piscina,
            garaje=garaje,
            ascensor=ascensor,
            vistas_mar=vistas_mar,
            vendido=vendido,
            alquiler=alquiler,
            url_detalle=url,
            inmobiliaria='Fincas Ciutadella',
            imagen_destacada=imagen_destacada,
            galeria=galeria
        )
    except Exception as e:
        print(f"Error scrapeando Fincas Ciutadella {url}: {e}")
        return None


def _pm_clean_int(txt):
    """Convierte textos tipo '1.010.000 €' o '181 m2' en enteros"""
    if not txt:
        return None
    s = (str(txt)
         .replace('\xa0', ' ')
         .replace('€','')
         .replace('m²','').replace('m2','').replace('m','')
         .replace('.','').replace(',','.')
         .strip())
    if s.endswith(('2','²')):
        s = s[:-1].strip()
    try:
        f = float(s)
        return int(round(f))
    except:
        return None

def _safe_text(el):
    return el.get_text(" ", strip=True) if el else ""


def scrape_mobilia_listado(url_listado, nombre):
    """
    Extrae propiedades directamente del listado (tabla #infoListado).
    Válido para Pons Morales y Finques Torres.
    """
    print(f"🏠 Iniciando scraping de {nombre} ({url_listado})")

    r = SESSION.get(url_listado, headers=HEADERS, timeout=30)
    r.raise_for_status()
    soup = BeautifulSoup(r.text, "lxml")

    filas = soup.select("#infoListado tbody > tr")
    if not filas:
        filas = soup.select("table#infoListado > tbody > tr, table#infoListado tr")

    propiedades = []
    total = len(filas)

    for idx, tr in enumerate(filas, 1):
        celdas = {}
        for td in tr.find_all("td", recursive=False):
            di = td.get("data-info")
            if di:
                celdas[di] = td

        enlace = tr.select_one("a[href*='/es/venta/ref-']")
        url_detalle = urljoin(url_listado, enlace["href"]) if enlace and enlace.has_attr("href") else ""

        referencia = _safe_text(celdas.get("referencia"))
        titulo = _safe_text(celdas.get("tituloInmueble"))

        tipo_el = tr.select_one("span[data-info='tipo']")
        tipo_raw = _safe_text(tipo_el).upper()
        tipo = detectar_tipo(tipo_raw)

        poblacion = _safe_text(celdas.get("poblacion"))
        zona = _safe_text(celdas.get("zona"))
        ubicacion = f"{poblacion}; {zona}" if poblacion and zona else (poblacion or zona)
        ubicacion = estandarizar_ubicacion(ubicacion)

        precio_el = celdas.get("precio")
        precio_txt = ""
        if precio_el:
            pv = precio_el.select_one("span[data-info='precioVenta']")
            precio_txt = _safe_text(pv) if pv else _safe_text(precio_el)
        precio = _pm_clean_int(precio_txt)

        sup_el = celdas.get("superficie")
        metros = None
        if sup_el and sup_el.has_attr("data-order"):
            metros = _pm_clean_int(sup_el["data-order"])
        else:
            metros = _pm_clean_int(_safe_text(sup_el)) if sup_el else None

        habitaciones = _pm_clean_int(_safe_text(celdas.get("dormitorios")))
        banos = _pm_clean_int(_safe_text(celdas.get("banos")))

        estado = ""
        vendido = False
        tag = tr.select_one(".ribbon .tag")
        if tag:
            t = _safe_text(tag).upper()
            if "VENDIDO" in t or "SOLD" in t:
                estado, vendido = "VENDIDO", True
            elif "RESERVADO" in t or "RESERVED" in t:
                estado = "RESERVADO"
            elif "EXCLUSIVA" in t or "EXCLUSIVE" in t:
                estado = "EXCLUSIVA"

        resumen = _safe_text(celdas.get("resumen"))
        blob = f"{titulo} {resumen}".upper()
        flags = detectar_flags(blob)
        piscina, garaje, ascensor, vistas_mar, alquiler = (
            flags['piscina'], flags['garaje'], flags['ascensor'], flags['vistas_mar'], flags['alquiler']
        )

        img = tr.select_one("td.foto img") or tr.select_one("img")
        imagen_src = ""
        if img:
            imagen_src = img.get("data-src") or img.get("src") or ""
            imagen_src = urljoin(url_listado, imagen_src)
        galeria = [imagen_src] if imagen_src else []
        imagen_destacada = galeria[0] if galeria else ""

        data = crear_propiedad_estandar(
            referencia=referencia,
            titulo=titulo,
            ubicacion=ubicacion,
            precio=precio,
            metros=metros,
            metros_parcela=None,
            habitaciones=habitaciones,
            banos=banos,
            tipo=tipo,
            estado=estado,
            piscina=piscina,
            garaje=garaje,
            ascensor=ascensor,
            vistas_mar=vistas_mar,
            vendido=vendido,
            alquiler=alquiler,
            url_detalle=url_detalle,
            inmobiliaria=nombre,
            imagen_destacada=imagen_destacada,
            galeria=galeria,
        )
        propiedades.append(data)
        print(f"  ✔ {idx}/{total} ref {referencia} -> {titulo}")

    return propiedades

def obtener_urls_inmomenorcacentro():
    """Obtener todas las URLs de propiedades de inmomenorcacentro desde el listado con sus referencias"""
    url_listado = "https://inmomenorcacentro.com/propiedades.php"
    try:
        r = SESSION.get(url_listado, headers=HEADERS, timeout=30)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, 'html.parser')

        urls_propiedades = []
        productos = soup.find_all('div', class_=lambda x: x and ('property' in str(x) or 'inmueble' in str(x)))

        if not productos:
            enlaces = soup.find_all('a', href=re.compile(r'propiedad\.php\?id=\d+'))
            for enlace in enlaces:
                href = enlace.get('href')
                contenedor = enlace.find_parent(['div', 'article', 'section'])
                referencia = None
                if contenedor:
                    match = re.search(r'REF[:\s]*(\d+)', contenedor.get_text(), re.IGNORECASE)
                    if match:
                        referencia = match.group(1)
                if not referencia:
                    id_match = re.search(r'id=(\d+)', href)
                    if id_match:
                        referencia = id_match.group(1)
                if referencia:
                    url_completa = urljoin(url_listado, href) if not href.startswith('http') else href
                    urls_propiedades.append((referencia, url_completa))
        else:
            for producto in productos:
                enlace = producto.find('a', href=re.compile(r'propiedad\.php\?id=\d+'))
                if not enlace:
                    continue
                href = enlace.get('href')
                referencia = None
                match = re.search(r'REF[:\s]*(\d+)', producto.get_text(), re.IGNORECASE)
                if match:
                    referencia = match.group(1)
                if not referencia:
                    id_match = re.search(r'id=(\d+)', href)
                    if id_match:
                        referencia = id_match.group(1)
                if referencia:
                    url_completa = urljoin(url_listado, href) if not href.startswith('http') else href
                    urls_propiedades.append((referencia, url_completa))

        return list(set(urls_propiedades))
    except Exception as e:
        print(f"Error obteniendo URLs de inmomenorcacentro: {e}")
        return []


def scrape_inmomenorcacentro_detalle(url, referencia):
    """Scraper específico para una propiedad de inmomenorcacentro.com"""
    try:
        r = SESSION.get(url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, 'html.parser')
        for tag in soup(["header", "footer"]):
            tag.decompose()

        # ===========================
        # TÍTULO
        # ===========================
        titulo = None
        titulo_tag = soup.select_one('.pull-left h3')
        if titulo_tag:
            titulo = titulo_tag.get_text(strip=True)

        # ===========================
        # PRECIO
        # ===========================
        precio = None
        for selector in ['.property-price','.precio','.price']:
            precio_tag = soup.select_one(selector)
            if precio_tag:
                precio_txt = re.sub(r'[^\d]', '', precio_tag.get_text(strip=True))
                if precio_txt.isdigit():
                    precio = int(precio_txt)
                    break
        if not precio:
            match = re.search(r'(\d{1,3}(?:[.,]\d{3})*)\s*€', soup.get_text())
            if match:
                precio = int(match.group(1).replace('.','').replace(',',''))

        # ===========================
        # UBICACIÓN
        # ===========================
        ubicacion = None
        ubicacion_tag = soup.select_one('.pull-left p')
        if ubicacion_tag:
            ubicacion = ubicacion_tag.get_text(strip=True)
        ubicacion = estandarizar_ubicacion(ubicacion)

        # ===========================
        # CARACTERÍSTICAS
        # ===========================
        habitaciones = banos = metros = metros_parcela = None
        caracteristicas_selectors = ['.facilities-list li','.property-details li','.caracteristicas li']
        for selector in caracteristicas_selectors:
            for item in soup.select(selector):
                texto = item.get_text(" ", strip=True).upper()
                if 'HABITACION' in texto or 'DORMITORIO' in texto:
                    m = re.search(r'(\d+)', texto)
                    if m: habitaciones = int(m.group(1))
                elif 'BAÑO' in texto or 'ASEO' in texto:
                    m = re.search(r'(\d+)', texto)
                    if m: banos = int(m.group(1))
                elif 'SUPERFICIE' in texto:
                    m = re.search(r'(\d+)', texto)
                    if m: metros = int(m.group(1))
                elif 'PARCELA' in texto or 'TERRENO' in texto:
                    m = re.search(r'(\d+)', texto)
                    if m: metros_parcela = int(m.group(1))

        # ===========================
        # ESTADO / FLAGS
        # ===========================
        texto_upper = soup.get_text().upper()
        flags = detectar_flags(texto_upper)
        piscina, garaje, ascensor, vistas_mar, alquiler = (
            flags['piscina'], flags['garaje'], flags['ascensor'], flags['vistas_mar'], flags['alquiler']
        )
        estado = None
        vendido = False
        if 'VENDIDO' in texto_upper:
            estado, vendido = 'VENDIDO', True
        elif 'RESERVADO' in texto_upper:
            estado = 'RESERVADO'

        # ===========================
        # GALERÍA
        # ===========================
        galeria = []
        for img in soup.select('.property-images img, .gallery img, img[src*="inmueble"]'):
            if img.has_attr('src'):
                src = img['src']
                if not any(x in src.lower() for x in ['logo','icon','banner']):
                    galeria.append(urljoin(url, src))
        imagen_destacada = galeria[0] if galeria else ''

        # ===========================
        # CREAR PROPIEDAD
        # ===========================
        tipo = detectar_tipo(titulo)
        return crear_propiedad_estandar(
            referencia=referencia,
            titulo=titulo,
            ubicacion=ubicacion,
            precio=precio,
            metros=metros,
            metros_parcela=metros_parcela,
            habitaciones=habitaciones,
            banos=banos,
            tipo=tipo,
            estado=estado,
            piscina=piscina,
            garaje=garaje,
            ascensor=ascensor,
            vistas_mar=vistas_mar,
            vendido=vendido,
            alquiler=alquiler,
            url_detalle=url,
            inmobiliaria='Inmo Menorca Centro',
            imagen_destacada=imagen_destacada,
            galeria=galeria
        )
    except Exception as e:
        print(f"Error scrapeando inmomenorcacentro {url}: {e}")
        return None

def obtener_urls_inmobiliariapalau():
    """Obtener todas las URLs de propiedades de Inmobiliaria Palau desde el sitemap"""
    sitemap_url = "https://inmobiliariapalau.com/propiedad-sitemap.xml"
    try:
        r = SESSION.get(sitemap_url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        root = ET.fromstring(r.content)

        urls_propiedades = []
        url_elements = root.findall(".//{http://www.sitemaps.org/schemas/sitemap/0.9}url")
        for url_element in url_elements:
            loc_element = url_element.find("{http://www.sitemaps.org/schemas/sitemap/0.9}loc")
            if loc_element is not None:
                url = loc_element.text
                if '/propiedad/' in url and url != "https://inmobiliariapalau.com/propiedad/":
                    referencia = None
                    match = re.search(r'/ref-(\d+)-', url)
                    if match:
                        referencia = match.group(1)
                    urls_propiedades.append((referencia, url))

        return list(set(urls_propiedades))
    except Exception as e:
        print(f"Error obteniendo URLs de Inmobiliaria Palau: {e}")
        return []


def scrape_inmobiliariapalau_detalle(url, referencia=None):
    """Scraper específico para una propiedad de inmobiliariapalau.com"""
    try:
        r = SESSION.get(url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, 'html.parser')
        for tag in soup(["header", "footer"]):
            tag.decompose()

        # REFERENCIA
        if not referencia:
            ref_tag = soup.find('p', class_='gb-headline-f29cb2dc')
            if ref_tag:
                referencia = re.sub(r'\D', '', ref_tag.get_text(strip=True))  # solo números

        # TÍTULO + UBICACIÓN
        titulo, ubicacion = None, None
        h1 = soup.find('h1')
        if h1:
            raw = h1.get_text(strip=True)
            raw = limpiar_texto(raw)
            m = re.search(r'(.+?)\s+en\s+(.+)$', raw, re.IGNORECASE)
            if m:
                titulo, ubicacion = limpiar_texto(m.group(1)), limpiar_texto(m.group(2))
            else:
                titulo = raw

        #fallback
        if not ubicacion:
            texto_completo = soup.get_text(" ", strip=True)

            localidades = {
                "mahón": "Maó",
                "mahon": "Maó",
                "mao": "Maó",
                "maó": "Maó",
                "ciutadella": "Ciutadella",
                "ciudadela": "Ciutadella",
                "ferreries": "Ferreries",
                "alaior": "Alaior",
                "mercadal": "Es Mercadal"
            }

            for patron, normalizado in localidades.items():
                if re.search(rf"\b{patron}\b", texto_completo, re.IGNORECASE):
                    ubicacion = normalizado
                    break

        ubicacion = estandarizar_ubicacion(ubicacion)

        # ===========================
        # PRECIO
        # ===========================
        precio = None
        precio_tag = soup.select_one('.fs-price')
        if precio_tag:
            txt = precio_tag.get_text(strip=True).replace('.', '').replace('€', '').replace(',', '').strip()
            if txt.isdigit():
                precio = int(txt)

        # ===========================
        # CARACTERÍSTICAS PRINCIPALES
        # ===========================
        habitaciones = banos = metros = metros_parcela = None
        hab_tag = soup.select_one('.gb-headline-37e4296c .gb-headline-text')
        if hab_tag and hab_tag.text.strip().isdigit():
            habitaciones = int(hab_tag.text.strip())

        bano_tag = soup.select_one('.gb-headline-48739d06 .gb-headline-text')
        if bano_tag and bano_tag.text.strip().isdigit():
            banos = int(bano_tag.text.strip())

        m2_tag = soup.select_one('.gb-headline-0503f08d .gb-headline-text')
        if m2_tag and m2_tag.text.strip().isdigit():
            metros = int(m2_tag.text.strip())

        # ===========================
        # FLAGS (piscina, garaje, etc.)
        # ===========================
        piscina = garaje = ascensor = vistas_mar = alquiler = False
        caracteristicas_block = soup.select_one('.caracteristicas-container')
        if caracteristicas_block:
            caracts = caracteristicas_block.get_text(" ", strip=True).upper()
            flags = detectar_flags(caracts)
            piscina, garaje, ascensor, vistas_mar, alquiler = (
                flags['piscina'], flags['garaje'], flags['ascensor'], flags['vistas_mar'], flags['alquiler']
            )

        # ===========================
        # ESTADO
        # ===========================
        estado = None
        vendido = False
        for span in soup.select("span.post-term-item"):
            classes = span.get("class", [])
            if "term-exclusiva" in classes:
                estado = "EXCLUSIVA"
            elif "term-vendida" in classes:
                estado, vendido = "VENDIDO", True
            elif "term-reservada" in classes:
                estado = "RESERVADO"

        # ===========================
        # GALERÍA
        # ===========================
        galeria, vistos = [], set()
        for selector in ['img[src*="wp-content"]','.wp-block-image img','.gallery img']:
            for img in soup.select(selector):
                if img.has_attr('src'):
                    src = img['src']
                    if not any(x in src.lower() for x in ['logo','icon','banner','favicon','avatar','facebook','twitter_X','linkedin','pinterest']):
                        abs_url = urljoin(url, src)
                        if abs_url not in vistos:
                            galeria.append(abs_url)
                            vistos.add(abs_url)
        imagen_destacada = galeria[0] if galeria else ''

        # ===========================
        # TIPO
        # ===========================
        tipo = None
        tipo_block = soup.select_one('.gb-headline-8ae34ab6 .gb-headline-text')
        if tipo_block:
            primer_span = tipo_block.find('span', class_='post-term-item')
            if primer_span:
                tipo = detectar_tipo(primer_span.get_text(strip=True).upper())

        # ===========================
        # CREAR PROPIEDAD
        # ===========================
        return crear_propiedad_estandar(
            referencia=referencia,
            titulo=titulo,
            ubicacion=ubicacion,
            precio=precio,
            metros=metros,
            metros_parcela=metros_parcela,
            habitaciones=habitaciones,
            banos=banos,
            tipo=tipo,
            estado=estado,
            piscina=piscina,
            garaje=garaje,
            ascensor=ascensor,
            vistas_mar=vistas_mar,
            vendido=vendido,
            alquiler=alquiler,
            url_detalle=url,
            inmobiliaria='Inmobiliaria Palau',
            imagen_destacada=imagen_destacada,
            galeria=galeria
        )
    except Exception as e:
        print(f"Error scrapeando Inmobiliaria Palau {url}: {e}")
        return None

def obtener_urls_bonninsanso():
    """Obtener URLs de propiedades de Bonnin Sanso desde sitemap"""
    sitemap_url = "https://www.bonninsanso.com/es/sitemap.xml"
    try:
        r = SESSION.get(sitemap_url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        root = ET.fromstring(r.content)

        urls_propiedades = []
        url_tags = root.findall(".//{http://www.sitemaps.org/schemas/sitemap/0.9}url")

        for url_tag in url_tags:
            loc = url_tag.find("{http://www.sitemaps.org/schemas/sitemap/0.9}loc")
            if (
                loc is not None 
                and "/es/compra/" in loc.text 
                and "mallorca" not in loc.text.lower()  # excluir Mallorca
            ):
                url = loc.text.strip()
                match = re.search(r'/(\d+)/?$', url)
                if match:
                    referencia = match.group(1)
                    urls_propiedades.append((referencia, url))

        return urls_propiedades
    except Exception as e:
        print(f"Error obteniendo URLs de Bonnin Sanso: {e}")
        return []


def scrape_bonninsanso_detalle(url, referencia):
    """Scraper específico para una propiedad de bonninsanso.com"""
    try:
        r = SESSION.get(url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, 'html.parser')

        contenido = soup.find("div", id="contenido")
        if contenido:
            soup = BeautifulSoup(str(contenido), 'html.parser')

        # ===========================
        # TÍTULO
        # ===========================
        titulo = None
        h1 = soup.find('h1')
        if h1:
            spans = h1.find_all('span')
            if len(spans) >= 2:
                titulo = spans[1].get_text(strip=True)
                titulo = titulo.replace(referencia, "", 1).strip()

        # ===========================
        # PRECIO
        # ===========================
        precio = None
        precio_elem = soup.select_one('.precio')
        if precio_elem:
            span = precio_elem.find('span')
            texto = span.next_sibling if span else precio_elem.get_text()
            if texto:
                precio_limpio = re.sub(r'[^\d]', '', texto)
                if precio_limpio.isdigit():
                    precio = int(precio_limpio)

        # ===========================
        # UBICACIÓN
        # ===========================
        ubicacion = None
        zona = soup.select_one('.info_zona b')
        if zona:
            ubicacion = zona.get_text(strip=True)
        ubicacion = estandarizar_ubicacion(ubicacion)

        # ===========================
        # CARACTERÍSTICAS
        # ===========================
        habitaciones = banos = metros = metros_parcela = None
        for img in soup.select('.caracteristicas-propiedad img'):
            texto = (img.get('title') or img.get('alt') or '').upper()
            src = img.get('src', '')
            if 'DORMITORIO' in texto or 'HABITACION' in texto or '/DORMITORIOS_' in src.upper():
                nums = re.findall(r'\d+', texto or src)
                if nums: habitaciones = int(nums[0])
            elif 'BAÑO' in texto or 'ASEO' in texto or '/BANOS_' in src.upper():
                nums = re.findall(r'\d+', texto or src)
                if nums: banos = int(nums[0])
            elif 'CONSTRUID' in texto or 'M²' in texto and not any(k in texto for k in ['PARCELA','SOLAR']):
                nums = re.findall(r'\d+', texto or src)
                if nums: metros = int(nums[0])
            elif 'PARCELA' in texto or 'TERRENO' in texto or 'SOLAR' in texto or 'SOLAR_WEB' in src.upper():
                nums = re.findall(r'\d+', texto or src)
                if nums: metros_parcela = int(nums[0])

        # fallback con regex en todo el texto
        texto_completo = soup.get_text()
        if not habitaciones:
            m = re.search(r'(\d+)\s*(?:habitacion|dormitorio)', texto_completo, re.IGNORECASE)
            if m: habitaciones = int(m.group(1))
        if not banos:
            m = re.search(r'(\d+)\s*baño', texto_completo, re.IGNORECASE)
            if m: banos = int(m.group(1))
        if not metros:
            m = re.search(r'(\d+)\s*m[2²]?\s*construid', texto_completo, re.IGNORECASE)
            if m: metros = int(m.group(1))

        # ===========================
        # ESTADO
        # ===========================
        estado = None
        vendido = False
        bandana = soup.find("div", class_="bandana")
        if bandana:
            estado = bandana.get_text(strip=True).upper()
        if estado and estado in ("VENDIDO","SOLD"):
            estado, vendido = "VENDIDO", True

        # ===========================
        # FLAGS
        # ===========================
        flags = detectar_flags(texto_completo.upper())
        piscina, garaje, ascensor, vistas_mar, alquiler = (
            flags['piscina'], flags['garaje'], flags['ascensor'], flags['vistas_mar'], flags['alquiler']
        )

        # ===========================
        # GALERÍA
        # ===========================
        galeria = []
        vistos = set()
        for a in soup.select('a[href]'):
            href = a.get('href', '')
            if (any(ext in href.lower() for ext in ['.jpg', '.jpeg', '.png', '.webp'])
                    and 'images.bonninsanso.com' in href
                    and href not in vistos):
                galeria.append(href)
                vistos.add(href)
        imagen_destacada = galeria[0] if galeria else ''

        # ===========================
        # CREAR PROPIEDAD
        # ===========================
        tipo = detectar_tipo(titulo)
        return crear_propiedad_estandar(
            referencia=referencia,
            titulo=titulo,
            ubicacion=ubicacion,
            precio=precio,
            metros=metros,
            metros_parcela=metros_parcela,
            habitaciones=habitaciones,
            banos=banos,
            tipo=tipo,
            estado=estado,
            piscina=piscina,
            garaje=garaje,
            ascensor=ascensor,
            vistas_mar=vistas_mar,
            vendido=vendido,
            alquiler=alquiler,
            url_detalle=url,
            inmobiliaria='Bonnin Sanso',
            imagen_destacada=imagen_destacada,
            galeria=galeria
        )
    except Exception as e:
        print(f"Error scrapeando Bonnin Sanso {url}: {e}")
        return None

def obtener_urls_fincasarmengol():
    """Obtener URLs de propiedades de Fincas Armengol desde el sitemap"""
    sitemap_url = "https://fincasarmengol.com/propiedad-sitemap.xml"
    try:
        r = SESSION.get(sitemap_url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        root = ET.fromstring(r.content)

        urls_propiedades = []
        url_tags = root.findall(".//{http://www.sitemaps.org/schemas/sitemap/0.9}url")
        for url_tag in url_tags:
            loc = url_tag.find("{http://www.sitemaps.org/schemas/sitemap/0.9}loc")
            if loc is not None and re.search(r'/propiedad/[^/]+/?$', loc.text.strip()):
                url = loc.text.strip()
                match = re.search(r'/propiedad/([^/]+)', url)
                referencia = match.group(1)[:10] if match else url.split("/")[-1]
                urls_propiedades.append((referencia, url))

        return urls_propiedades
    except Exception as e:
        print(f"Error obteniendo URLs de Fincas Armengol: {e}")
        return []


def scrape_fincasarmengol_detalle(url, referencia):
    """Scraper específico para una propiedad de fincasarmengol.com"""
    try:
        r = SESSION.get(url, headers=HEADERS, timeout=30)
        # Algunas fichas dan "error crítico" de WordPress al final de la página (HTTP 500)
        # pero traen la ficha completa: se aceptan si contienen los atributos
        if not (r.status_code == 500 and 'property_attributes' in r.text):
            r.raise_for_status()
        soup = BeautifulSoup(r.text, 'html.parser')
        for tag in soup(["header","footer"]):
            tag.decompose()

        # ===========================
        # ATRIBUTOS ("<b>Etiqueta:</b> valor<br>")
        # ===========================
        atributos = {}
        bloque = soup.select_one("div.property_attributes")
        if bloque:
            for b in bloque.find_all("b"):
                etiqueta = b.get_text(strip=True).rstrip(':').strip().lower()
                valor = []
                for sib in b.next_siblings:
                    if getattr(sib, 'name', None) in ('b', 'br', 'div'):
                        break
                    valor.append(sib.get_text() if hasattr(sib, 'get_text') else str(sib))
                atributos[etiqueta] = re.sub(r'\s+', ' ', ''.join(valor)).strip()

        def num_atributo(*claves):
            for clave in claves:
                m = re.search(r'\d[\d.]*', atributos.get(clave, ''))
                if m:
                    return int(m.group().replace('.', ''))
            return None

        # ===========================
        # TÍTULO + UBICACIÓN
        # ===========================
        # Formatos: "C-8108 Casa – Ciutadella", "Casa de Campo en  Alaior  M-7117",
        #           "C-058 (1) Restaurante - Cap d'Artruix", "Solar/Terreno en Mahón    M-9159"
        patron_ref = r'\b[A-Z]{1,2}\s?-\s?\d+(?:\s*\(\d+\))?'
        titulo, ubicacion = None, None
        titulo_elem = soup.select_one("h2")
        raw = titulo_elem.get_text(" ", strip=True) if titulo_elem else ''
        ref_titulo = re.search(patron_ref, raw)
        raw = re.sub(patron_ref, ' ', raw)
        raw = re.sub(r'\s*[–—]\s*', ' - ', raw)
        raw = re.sub(r'\s+', ' ', raw).strip(' -')
        raw = re.sub(r'^[A-Z]\s+|\s+-?[A-Z]$', '', raw)  # letras sueltas de variantes ("-A", "B Piso...")
        if raw:
            partes = [p.strip() for p in raw.split(' - ') if p.strip()]
            m = re.search(r'\ben\s+([^\-]+)$', raw, re.IGNORECASE)
            if len(partes) > 1:
                ubicacion, titulo = partes[-1], " - ".join(partes[:-1])
            elif m:
                ubicacion, titulo = m.group(1).strip(), raw
            else:
                titulo = raw

        # El campo "Ubicación" de la ficha, si algún día viene relleno, tiene prioridad
        if atributos.get('ubicación'):
            ubicacion = atributos['ubicación']

        # Sin ubicación: la letra de la referencia indica la oficina (C = Ciutadella, M = Maó)
        ref_texto = atributos.get('referencia') or (ref_titulo.group() if ref_titulo else '')
        if not ubicacion and ref_texto:
            ubicacion = {'C': 'Ciutadella', 'M': 'Maó'}.get(ref_texto.strip()[:1].upper())
        if ubicacion:
            ubicacion = ubicacion.replace('’', "'").replace('´', "'")
            ubicacion = re.sub(r'\(.*?\)|:.*$', '', ubicacion)  # "Mahón (Obra Nueva)", "Cala Blanca: Piscina..."
            ubicacion = re.sub(r'^(el\s+)?centro\s+(de|del)\s+', '', ubicacion.strip(), flags=re.IGNORECASE)
            ubicacion = re.sub(r',?\s*Menorca$', '', ubicacion, flags=re.IGNORECASE).strip(' ,-')
        ubicacion = estandarizar_ubicacion(ubicacion)

        # ===========================
        # PRECIO + ESTADO
        # ===========================
        precio_txt = atributos.get('precio', '')
        precio = None
        m = re.search(r'(\d{1,3}(?:[.,]\d{3})+|\d+)\s*€', precio_txt)
        if m:
            precio = int(re.sub(r'[.,]', '', m.group(1)))

        estado = None
        vendido = False
        for texto_estado in (precio_txt, titulo_elem.get_text(" ", strip=True) if titulo_elem else ''):
            m = PATRON_NO_DISPONIBLE.search(texto_estado or '')
            if m:
                estado = 'RESERVADO' if m.group(1).upper().startswith('RESERV') else 'VENDIDO'
                vendido = True
                break

        # ===========================
        # CARACTERÍSTICAS
        # ===========================
        habitaciones = num_atributo('habitaciones', 'dormitorios')
        banos = num_atributo('baños', 'banos')
        metros = num_atributo('área construida', 'superficie construida')
        metros_parcela = num_atributo('área de la parcela', 'parcela')

        # ===========================
        # FLAGS
        # ===========================
        descripcion = bloque.find('p').get_text(" ", strip=True) if bloque and bloque.find('p') else ''
        flags = detectar_flags(f"{titulo or ''} {descripcion} {atributos.get('otros', '')}".upper())
        piscina, garaje, ascensor, vistas_mar, alquiler = (
            flags['piscina'], flags['garaje'], flags['ascensor'], flags['vistas_mar'], flags['alquiler']
        )

        # ===========================
        # GALERÍA
        # ===========================
        galeria = []
        vistos = set()
        for img in soup.select('img'):
            src = img.get('data-src') or img.get('src') or ''
            if 'wp-content/uploads' not in src or 'q_lqip' in src:
                continue
            if any(x in src.lower() for x in ['logo','icon','banner','/flags/']):
                continue
            abs_url = urljoin(url, src)
            if abs_url not in vistos:
                galeria.append(abs_url)
                vistos.add(abs_url)
        imagen_destacada = galeria[0] if galeria else ''

        # ===========================
        # CREAR PROPIEDAD
        # ===========================
        tipo = detectar_tipo(f"{titulo or ''} {atributos.get('tipo de propiedad', '')}")
        return crear_propiedad_estandar(
            referencia=referencia,
            titulo=titulo,
            ubicacion=ubicacion,
            precio=precio,
            metros=metros,
            metros_parcela=metros_parcela,
            habitaciones=habitaciones,
            banos=banos,
            tipo=tipo,
            estado=estado,
            piscina=piscina,
            garaje=garaje,
            ascensor=ascensor,
            vistas_mar=vistas_mar,
            vendido=vendido,
            alquiler=alquiler,
            url_detalle=url,
            inmobiliaria='Fincas Armengol',
            imagen_destacada=imagen_destacada,
            galeria=galeria
        )
    except Exception as e:
        print(f"Error scrapeando Fincas Armengol {url}: {e}")
        return None

def obtener_urls_fincasfaro():
    """Obtener URLs de propiedades de Fincas Faro desde el sitemap"""
    sitemap_url = "https://fincasfaro.net/es/sitemap.xml"
    try:
        r = SESSION.get(sitemap_url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        root = ET.fromstring(r.content)

        urls_propiedades = []
        url_tags = root.findall(".//{http://www.sitemaps.org/schemas/sitemap/0.9}url")
        for url_tag in url_tags:
            loc = url_tag.find("{http://www.sitemaps.org/schemas/sitemap/0.9}loc")
            if loc is not None and "/es/ficha/" in loc.text:
                url = loc.text.strip()
                match = re.search(r'/(\d+)/?$', url)
                if match:
                    referencia = match.group(1)
                else:
                    ref = url.split("/")[-1] or url.split("/")[-2]
                    referencia = ref[:10]
                urls_propiedades.append((referencia, url))

        return urls_propiedades
    except Exception as e:
        print(f"Error obteniendo URLs de Fincas Faro: {e}")
        return []


def scrape_fincasfaro_detalle(url, referencia):
    """Scraper específico para una propiedad de fincasfaro.net"""
    try:
        r = SESSION.get(url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, 'html.parser')

        contenido = soup.find("div", id="contenido")
        if contenido:
            soup = BeautifulSoup(str(contenido), 'html.parser')

        texto_completo = soup.get_text()

        # ===========================
        # TÍTULO
        # ===========================
        titulo = None
        titulo_elem = soup.select_one('h1')
        if titulo_elem:
            for sp in titulo_elem.find_all('span'):
                sp.decompose()
            titulo = titulo_elem.get_text(strip=True)

        #referencia
        ref_tag = soup.select_one(".foto_flotada_izquierda_portada.ficha .texto_columna h1 span.referencia")
        if ref_tag:
            texto = ref_tag.get_text(strip=True)  # "Ref. 1593V - Venta"
            # Eliminar "Ref." al inicio y "- Venta" al final
            referencia = re.sub(r"^Ref\.\s*", "", texto)      # quita "Ref."
            referencia = re.sub(r"\s*-\s*Venta$", "", referencia)  # quita "- Venta"


        # ===========================
        # PRECIO
        # ===========================
        precio = None
        precio_elem = soup.select_one('.precio_propiedad')
        if precio_elem:
            # Tomar solo el primer nodo de texto (ignorar <del>)
            primer_texto = precio_elem.find(text=True, recursive=False)
            if primer_texto:
                precio_txt = primer_texto.strip()
                precio_limpio = re.sub(r'[^\d]', '', precio_txt)
                if precio_limpio.isdigit():
                    precio = int(precio_limpio)


        # ===========================
        # UBICACIÓN
        # ===========================
        ubicacion = None
        ubicacion_tags = soup.select('.lugar')
        if ubicacion_tags:
            ubicacion = ubicacion_tags[0].get_text(strip=True)  # solo el primero
            ubicacion = estandarizar_ubicacion(ubicacion)

        # ===========================
        # CARACTERÍSTICAS
        # ===========================
        habitaciones = banos = metros = metros_parcela = None
        for li in soup.select('.caracteristicas_principales li'):
            label = li.get_text(strip=True).upper()
            value = li.find('strong')
            if not value:
                continue
            texto_valor = value.get_text(strip=True)

            limpio = (texto_valor.replace('m²','').replace('m2','')
                                   .replace('m','').replace('.','')
                                   .replace(',','').strip())
            if limpio.endswith(('2','²')):
                limpio = limpio[:-1].strip()

            if 'DORMITORIO' in label and limpio.isdigit():
                habitaciones = int(limpio)
            elif ('BAÑO' in label or 'ASEO' in label) and limpio.isdigit():
                banos = int(limpio)
            elif ('METROS EDIF' in label or 'CONSTRUID' in label) and limpio.isdigit():
                metros = int(limpio)
            elif any(k in label for k in ['METROS SOLAR','PARCELA','TERRENO']) and limpio.isdigit():
                metros_parcela = int(limpio)

        # ===========================
        # ESTADO
        # ===========================
        estado = None
        vendido = 'VENDIDO' in texto_completo.upper()

        # ===========================
        # FLAGS
        # ===========================
        flags = detectar_flags(texto_completo.upper())
        piscina, garaje, ascensor, vistas_mar, alquiler = (
            flags['piscina'], flags['garaje'], flags['ascensor'], flags['vistas_mar'], flags['alquiler']
        )

        # ===========================
        # GALERÍA
        # ===========================
        galeria = []
        vistos = {}
        excluir = ['logo','icon','banner','/flags/','/static/']

        for img in soup.select('img'):
            url_rel, w = None, 0
            srcset = img.get('data-srcset') or img.get('srcset')
            if srcset:
                candidatos = []
                for part in srcset.split(','):
                    m = re.match(r'(\S+)\s+(\d+)(w|x)', part.strip())
                    if m:
                        url_tmp, num, suf = m.groups()
                        ancho = int(num) * (1000 if suf == 'x' else 1)
                        candidatos.append((ancho, url_tmp))
                    else:
                        candidatos.append((0, part.split()[0]))
                if candidatos:
                    candidatos.sort(key=lambda t: t[0])
                    w, url_rel = candidatos[-1]

            if not url_rel:
                for attr in ['data-src','data-lazy','data-original','src']:
                    if img.has_attr(attr):
                        url_rel = img[attr]
                        break
            if not url_rel:
                continue

            abs_url = urljoin(url, url_rel)
            if any(x in abs_url.lower() for x in excluir):
                continue
            clave = re.sub(r'/\d+x\d+(?=[^\d]|$)', '', abs_url)
            if clave not in vistos or w > vistos[clave][0]:
                vistos[clave] = (w, abs_url)

        galeria = [v[1] for v in vistos.values()]
        imagen_destacada = galeria[0] if galeria else ''

        # ===========================
        # CREAR PROPIEDAD
        # ===========================
        tipo = detectar_tipo(titulo)
        return crear_propiedad_estandar(
            referencia=referencia,
            titulo=titulo,
            ubicacion=ubicacion,
            precio=precio,
            metros=metros,
            metros_parcela=metros_parcela,
            habitaciones=habitaciones,
            banos=banos,
            tipo=tipo,
            estado="VENDIDO" if vendido else estado,
            piscina=piscina,
            garaje=garaje,
            ascensor=ascensor,
            vistas_mar=vistas_mar,
            vendido=vendido,
            alquiler=alquiler,
            url_detalle=url,
            inmobiliaria='Fincas Faro',
            imagen_destacada=imagen_destacada,
            galeria=galeria
        )
    except Exception as e:
        print(f"Error scrapeando Fincas Faro {url}: {e}")
        return None

def obtener_urls_zenhousecredit():
    """Obtener todas las URLs de propiedades de Zenhouse Credit desde el listado con sus referencias"""
    url_listado = "https://zenhousecredit.com/venta.php"
    try:
        r = SESSION.get(url_listado, headers=HEADERS, timeout=30)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, 'html.parser')

        urls_propiedades = []
        productos = soup.find_all('article', class_='property-item clearfix')

        for producto in productos:
            enlace = producto.find('a', href=re.compile(r'propiedad\.php\?id=\d+'))
            referencia_elemento = producto.select_one('h4')
            if enlace and referencia_elemento:
                href = enlace.get('href')
                referencia_texto = referencia_elemento.get_text(strip=True)
                match = re.match(r'^\d+', referencia_texto)
                if match:
                    referencia = match.group(0)
                    url_completa = href if href.startswith('http') else urljoin(url_listado, href)
                    urls_propiedades.append((referencia, url_completa))

        return list(set(urls_propiedades))
    except Exception as e:
        print(f"Error obteniendo URLs de Zenhouse Credit: {e}")
        return []


def scrape_zenhousecredit_detalle(url, referencia):
    """Scraper específico para una propiedad de zenhousecredit.com"""
    try:
        r = SESSION.get(url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, 'html.parser')
        for tag in soup(["header","footer"]):
            tag.decompose()

        texto_completo = soup.get_text(" ", strip=True)

        # ===========================
        # TÍTULO
        # ===========================
        titulo = None
        h1 = soup.select_one(".wrap h4.title")
        if h1:
            titulo = h1.get_text(strip=True)
            if titulo:
                titulo = re.sub(referencia, "", titulo).strip()

        # ===========================
        # PRECIO
        # ===========================
        precio = None
        for pattern in [r'(\d{1,3}(?:[.,]\d{3})*)\s*€', r'€\s*(\d{1,3}(?:[.,]\d{3})*)']:
            match = re.search(pattern, texto_completo)
            if match:
                precio_str = match.group(1).replace('.', '').replace(',', '')
                if precio_str.isdigit():
                    precio = int(precio_str)
                    break

        # ===========================
        # UBICACIÓN
        # ===========================
        ubicacion = None
        features = soup.select(".features ul li")
        ubic_parts = []
        for li in features:
            text = li.get_text(" ", strip=True)
            if "Localidad:" in text or "Zona:" in text:
                ubic_parts.append(text.split(":",1)[1].strip())
        if ubic_parts:
            ubicacion = "; ".join(ubic_parts)
        ubicacion = estandarizar_ubicacion(ubicacion)

        # ===========================
        # CARACTERÍSTICAS
        # ===========================
        metros = metros_parcela = habitaciones = banos = None
        for sp in soup.select(".property-meta span"):
            txt = sp.get_text(strip=True).lower()
            if "m2" in txt:
                m = re.findall(r"\d+", txt)
                if m: metros = int(m[0])
            elif "dormitorio" in txt:
                m = re.findall(r"\d+", txt)
                if m: habitaciones = int(m[0])
            elif "bañ" in txt:
                m = re.findall(r"\d+", txt)
                if m: banos = int(m[0])
        for li in features:
            txt = li.get_text(strip=True).lower()
            if "superficie" in txt:
                m = re.search(r'(\d+)', txt)
                if m: metros = int(m.group(1))
            elif "parcela" in txt or "terreno" in txt:
                m = re.search(r'(\d+)', txt)
                if m: metros_parcela = int(m.group(1))

        # ===========================
        # ESTADO
        # ===========================
        texto_upper = texto_completo.upper()
        estado = None
        vendido = False
        if "VENDIDO" in texto_upper:
            estado, vendido = "VENDIDO", True

        # ===========================
        # FLAGS
        # ===========================
        flags = detectar_flags(texto_upper)
        piscina, garaje, ascensor, vistas_mar, alquiler = (
            flags['piscina'], flags['garaje'], flags['ascensor'], flags['vistas_mar'], flags['alquiler']
        )

        # ===========================
        # GALERÍA
        # ===========================
        galeria = []
        for selector in [
            'img[src*="propiedad"]','.gallery img','.images img',
            'img:not([src*="logo"]):not([src*="icon"]):not([src*="banner"])'
        ]:
            for img in soup.select(selector):
                if img.has_attr('src'):
                    src = img['src']
                    if not any(x in src.lower() for x in ['logo','icon','banner','menu','wapp']):
                        abs_url = urljoin(url, src)
                        if abs_url not in galeria:
                            galeria.append(abs_url)
        imagen_destacada = galeria[0] if galeria else ''

        # ===========================
        # CREAR PROPIEDAD
        # ===========================
        tipo = detectar_tipo(titulo)
        return crear_propiedad_estandar(
            referencia=referencia,
            titulo=titulo,
            ubicacion=ubicacion,
            precio=precio,
            metros=metros,
            metros_parcela=metros_parcela,
            habitaciones=habitaciones,
            banos=banos,
            tipo=tipo,
            estado=estado,
            piscina=piscina,
            garaje=garaje,
            ascensor=ascensor,
            vistas_mar=vistas_mar,
            vendido=vendido,
            alquiler=alquiler,
            url_detalle=url,
            inmobiliaria='Zenhouse Credit',
            imagen_destacada=imagen_destacada,
            galeria=galeria
        )
    except Exception as e:
        print(f"Error scrapeando Zenhouse Credit {url}: {e}")
        return None

def obtener_urls_enprimeralinea():
    """Obtener URLs de propiedades de En Primera Línea desde el sitemap"""
    sitemap_url = "https://enprimeralinea.immo/sitemap.xml"
    try:
        r = SESSION.get(sitemap_url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        root = ET.fromstring(r.content)

        urls_propiedades = []
        url_tags = root.findall(".//{http://www.sitemaps.org/schemas/sitemap/0.9}url")
        for url_tag in url_tags:
            loc = url_tag.find("{http://www.sitemaps.org/schemas/sitemap/0.9}loc")
            if loc is None:  # ← CORRECCIÓN: usar 'is None' en lugar de 'not loc'
                continue
            url = loc.text.strip()
            # excluir idiomas (/gb/, /ru/, /cat/, etc.)
            if re.search(r"/[a-z]{2}/", url):
                continue
            if re.search(r"-es\d{4,}\.html$", url):
                # ← CORRECCIÓN: extraer referencia y devolver tupla (referencia, url)
                referencia = url.split("-")[-1].replace(".html", "")
                urls_propiedades.append((referencia, url))

        return urls_propiedades
    except Exception as e:
        print(f"Error obteniendo URLs de En Primera Línea: {e}")
        return []


def scrape_enprimeralinea_detalle(url, referencia=None):
    """Scraper específico para una propiedad de enprimeralinea.immo"""
    try:
        r = SESSION.get(url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, 'html.parser')
        for tag in soup(["header","footer"]):
            tag.decompose()

        # ===========================
        # TÍTULO
        # ===========================
        titulo = None
        h3 = soup.select_one('#descripcionFicha h3')
        if h3:
            titulo = h3.get_text(strip=True)

        ref_tag = soup.select_one('.headerLeft p span')
        if ref_tag:
            referencia = ref_tag.get_text(strip=True)

        # ===========================
        # UBICACIÓN
        # ===========================
        ubicacion = None
        poblacion = zona = None
        for li in soup.select('.detallesFicha ul li'):
            strong = li.find('strong')
            if not strong:
                continue
            key = strong.get_text(strip=True).upper()
            val = li.get_text(" ", strip=True).replace(strong.get_text(strip=True), "").strip()
            if 'POBLACIÓN' in key:
                poblacion = val
            elif 'ZONA' in key:
                zona = val
        if poblacion and zona:
            ubicacion = f"{poblacion}; {zona}"
        elif poblacion:
            ubicacion = poblacion
        elif zona:
            ubicacion = zona
        ubicacion = estandarizar_ubicacion(ubicacion)

        # ===========================
        # PRECIO
        # ===========================
        precio = None
        match = re.search(r'(\d{1,3}(?:[.,]\d{3})*)\s*€', soup.get_text())
        if match:
            precio = int(match.group(1).replace('.','').replace(',',''))

        # ===========================
        # CARACTERÍSTICAS
        # ===========================
        habitaciones = banos = metros = metros_parcela = None
        for li in soup.select('.detallesFicha ul li'):
            strong = li.find('strong')
            if not strong:
                continue
            key = strong.get_text(strip=True).upper()
            val = li.get_text(" ", strip=True).replace(strong.get_text(strip=True), "").strip()
            if 'HABITACIONES' in key:
                nums = re.findall(r'\d+', val)
                if nums: habitaciones = int(nums[0])
            elif 'BAÑOS' in key:
                nums = re.findall(r'\d+', val)
                if nums: banos = int(nums[0])
            elif 'SUP. CONSTRUIDA' in key:
                nums = re.findall(r'\d+', val)
                if nums: metros = int(nums[0])
            elif 'SUP. PARCELA' in key:
                nums = re.findall(r'\d+', val)
                if nums: metros_parcela = int(nums[0])

        # ===========================
        # ESTADO
        # ===========================
        estado = None
        vendido = False
        etiqueta = soup.select_one('#etiqueta .etiqueta')
        if etiqueta:
            txt = etiqueta.get_text(strip=True).upper()
            if 'VENDIDO' in txt:
                estado, vendido = 'VENDIDO', True
            elif 'RESERVADO' in txt:
                estado, vendido = 'RESERVADO', True
            elif txt not in ['DISPONIBLE','NOVEDAD']:
                estado = txt

        # ===========================
        # FLAGS
        # ===========================
        flags = detectar_flags(soup.get_text().upper())
        piscina, garaje, ascensor, vistas_mar, alquiler = (
            flags['piscina'], flags['garaje'], flags['ascensor'], flags['vistas_mar'], flags['alquiler']
        )

        # ===========================
        # GALERÍA
        # ===========================
        galeria = []
        vistos = set()
        for img in soup.select('img'):
            if img.has_attr('src'):
                src = img['src']
                if not any(x in src.lower() for x in ['logo','icon','banner','caracts','assets']):
                    abs_url = urljoin(url, src)
                    if abs_url not in vistos:
                        galeria.append(abs_url)
                        vistos.add(abs_url)
        imagen_destacada = galeria[0] if galeria else ''

        # ===========================
        # CREAR PROPIEDAD
        # ===========================
        tipo = detectar_tipo(titulo)
        return crear_propiedad_estandar(
            referencia=referencia,
            titulo=titulo,
            ubicacion=ubicacion,
            precio=precio,
            metros=metros,
            metros_parcela=metros_parcela,
            habitaciones=habitaciones,
            banos=banos,
            tipo=tipo,
            estado=estado,
            piscina=piscina,
            garaje=garaje,
            ascensor=ascensor,
            vistas_mar=vistas_mar,
            vendido=vendido,
            alquiler=alquiler,
            url_detalle=url,
            inmobiliaria='En Primera Linea',
            imagen_destacada=imagen_destacada,
            galeria=galeria
        )
    except Exception as e:
        print(f"Error scrapeando En Primera Línea {url}: {e}")
        return None

def obtener_urls_casasenmenorca():
    """Obtener URLs de propiedades de Casas en Menorca desde el sitemap"""
    sitemap_url = "https://www.casasenmenorca.com/sitemap-es-es.xml"
    try:
        r = SESSION.get(sitemap_url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        root = ET.fromstring(r.content)

        ns = {
            'sm': "http://www.sitemaps.org/schemas/sitemap/0.9",
            'image': "http://www.google.com/schemas/sitemap-image/1.1"
        }

        urls_propiedades = []
        for url_tag in root.findall("sm:url", ns):
            loc = url_tag.find("sm:loc", ns)
            if loc is None:  # ← CORRECCIÓN: usar 'is None' en lugar de 'not loc'
                continue
            url = loc.text.strip()
            if "/inmueble/" not in url:
                continue
            
            # ← CORRECCIÓN: extraer referencia de la URL
            referencia = url.split("/")[-1] if not url.endswith("/") else url.split("/")[-2]
            if not referencia:
                referencia = "unknown"
            
            # ← CORRECCIÓN: devolver solo tupla (referencia, url)
            urls_propiedades.append((referencia, url))

        return urls_propiedades
    except Exception as e:
        print(f"Error obteniendo URLs de Casas en Menorca: {e}")
        return []


def scrape_casasenmenorca_detalle(url, referencia=None):
    """Scraper específico para una propiedad de Casas en Menorca usando JSON-LD"""
    # ← CORRECCIÓN: cambiar parámetro de imagen_destacada a referencia
    try:
        r = SESSION.get(url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, 'html.parser')

        json_blocks = soup.find_all("script", type="application/ld+json")
        data_listing = data_breadcrumb = None

        for block in json_blocks:
            try:
                data = json.loads(block.string)
            except Exception:
                continue
            if not isinstance(data, dict):
                continue
            if data.get("@type") == "RealEstateListing":
                data_listing = data
            elif data.get("@type") == "BreadcrumbList":
                data_breadcrumb = data

        if not data_listing:
            print(f"No JSON-LD RealEstateListing en {url}")
            return None

        # TÍTULO / REFERENCIA / PRECIO
        titulo = data_listing.get("name")
        descripcion = data_listing.get("description")

        if not referencia:
            match = re.search(r'/(\d+)$', data_listing.get("url", ""))
            if match:
                referencia = match.group(1)

        precio = None
        offers = data_listing.get("offers", {})
        if isinstance(offers, dict):
            precio_str = offers.get("price")
            if precio_str and str(precio_str).isdigit():
                precio = int(precio_str)

        # UBICACIÓN (breadcrumb)
        ubicacion = None
        if data_breadcrumb:
            items = [it.get("name") for it in data_breadcrumb.get("itemListElement", []) if it.get("name")]
            if len(items) > 2:
                items = items[2:-1]
            seen = set()
            ubic_list = []
            for it in items:
                if it not in seen:
                    ubic_list.append(it)
                    seen.add(it)
            if ubic_list:
                ubicacion = "; ".join(ubic_list)
                ubicacion = estandarizar_ubicacion(ubicacion)

        # CARACTERÍSTICAS (desde descripción)
        habitaciones = banos = metros = metros_parcela = None
        if descripcion:
            desc = descripcion.lower()
            m = re.search(r'(\d+)\s*(?:habitaciones?|dormitorios?)', desc)
            if m: habitaciones = int(m.group(1))
            m = re.search(r'(\d+)\s*(?:baños?|aseos?)', desc)
            if m: banos = int(m.group(1))
            m = re.search(r'(\d[\d\.,]*)\s*(?:m2|m²)', desc)
            if m:
                try: metros = int(m.group(1).replace('.','').replace(',',''))
                except: pass
            m = re.search(r'(\d[\d\.,]*)\s*(?:m2|m²).*(parcela|solar|terreno)', desc)
            if m:
                try: metros_parcela = int(m.group(1).replace('.','').replace(',',''))
                except: pass

        # GALERÍA
        galeria = []
        if data_listing.get("image"):
            if isinstance(data_listing["image"], list):
                galeria = data_listing["image"]
            else:
                galeria = [data_listing["image"]]
        imagen_final = galeria[0] if galeria else None

        # ESTADO
        estado = None
        vendido = False
        for st in soup.select('.stickerRender .stickerText'):
            txt = st.get_text(strip=True).upper()
            if 'VENDIDO' in txt or 'RESERVADO' in txt:
                estado, vendido = 'VENDIDO', True
            elif txt not in ['DISPONIBLE','NOVEDAD']:
                estado = txt

        # FLAGS
        flags = detectar_flags(soup.get_text().upper())
        piscina, garaje, ascensor, vistas_mar, alquiler = (
            flags['piscina'], flags['garaje'], flags['ascensor'], flags['vistas_mar'], flags['alquiler']
        )

        alquiler = False

        if data_breadcrumb:
            items = data_breadcrumb.get("itemListElement", [])
            for it in items:
                nombre = it.get("name", "").lower()
                if "alquiler" in nombre or "rent" in nombre:
                    alquiler = True
                    break


        # CREAR PROPIEDAD
        tipo = detectar_tipo(titulo)
        return crear_propiedad_estandar(
            referencia=referencia,
            titulo=titulo,
            ubicacion=ubicacion,
            precio=precio,
            metros=metros,
            metros_parcela=metros_parcela,
            habitaciones=habitaciones,
            banos=banos,
            tipo=tipo,
            estado=estado,
            piscina=piscina,
            garaje=garaje,
            ascensor=ascensor,
            vistas_mar=vistas_mar,
            vendido=vendido,
            alquiler=alquiler,
            url_detalle=url,
            inmobiliaria="Casas en Menorca",
            imagen_destacada=imagen_final,
            galeria=galeria
        )
    except Exception as e:
        print(f"Error scrapeando Casas en Menorca {url}: {e}")
        return None


def obtener_urls_fincasseminari(max_paginas=5):
    """Obtener todas las URLs de propiedades de Fincas Seminari recorriendo paginación"""
    base_url = "https://www.fincasseminari.com/venta.php"
    urls_propiedades = []

    for nump in range(1, max_paginas+1):
        url_listado = f"{base_url}?&nump={nump}"
        try:
            r = SESSION.get(url_listado, headers=HEADERS, timeout=30)
            r.raise_for_status()
            soup = BeautifulSoup(r.text, "html.parser")

            items = soup.select("div.item-wrap")
            if not items:  # si ya no hay resultados → parar
                break

            for item in items:
                enlace = item.select_one("a[href*='propiedad-venta.php']")
                h6_tags = item.find_all("h6")
                referencia = None
                estado = None

                if h6_tags:
                    ref_text = h6_tags[0].get_text(strip=True)
                    m = re.search(r'(\d[\w-]*)', ref_text)
                    if m:
                        referencia = m.group(1)

                # Capturar estado desde el listado
                estado_tag = item.select_one("span.label")
                if estado_tag:
                    txt = estado_tag.get_text(strip=True).upper()
                    if txt not in ["NOVEDAD"]:  # omitimos novedad
                        estado = txt

                if enlace and referencia:
                    url_detalle = urljoin(base_url, enlace["href"])
                    # Retornar (referencia, url) pero guardar estado en un diccionario global
                    _estados_fincasseminari[url_detalle] = estado
                    urls_propiedades.append((referencia, url_detalle))
            
            time.sleep(1)

        except Exception as e:
            print(f"Error en página {nump}: {e}")
            break

    return list(set(urls_propiedades))


def scrape_fincasseminari_detalle(url, referencia=None):
    """Scraper específico para una propiedad de fincasseminari.com"""
    try:
        r = SESSION.get(url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, "html.parser")
        for tag in soup(["header","footer"]):
            tag.decompose()

        texto_completo = soup.get_text(" ", strip=True).upper()

        # REFERENCIA
        if not referencia:
            ref_tag = soup.select_one(".detail-amenities-list li .media-body")
            if ref_tag and "REF" in ref_tag.get_text().upper():
                referencia = re.sub(r"[^\w\.-]", "", ref_tag.get_text())

        # TÍTULO
        titulo = None
        titulo_tag = soup.select_one(".property-description h3 span")
        if titulo_tag:
            titulo = titulo_tag.get_text(strip=True)

        # UBICACIÓN
        ubicacion = None
        zona_tag = soup.find("div", class_="media-body", string=re.compile("Zona", re.I))
        if not zona_tag:
            for li in soup.select(".detail-amenities-list li .media-body"):
                if "zona" in li.get_text(strip=True).lower():
                    ubicacion = li.get_text(strip=True).replace("Zona", "").strip()
                    break
        else:
            ubicacion = zona_tag.get_text(strip=True)

        # 🔽 Nueva lógica para invertir
        if ubicacion and ";" in ubicacion:
            partes = [p.strip() for p in ubicacion.split(";")]
            ubicacion = "; ".join(reversed(partes))

        ubicacion = estandarizar_ubicacion(ubicacion)

        # PRECIO
        precio = None
        precio_tag = soup.select_one(".detail-bar .title-right h3")
        if precio_tag:
            precio_txt = re.sub(r"[^\d]", "", precio_tag.get_text(strip=True))
            if precio_txt.isdigit():
                precio = int(precio_txt)

        # CARACTERÍSTICAS
        habitaciones = banos = metros = metros_parcela = None
        for li in soup.select(".detail-amenities-list li .media-body"):
            txt = li.get_text(" ", strip=True).lower()
            if "habitacion" in txt or "dormitorio" in txt:
                m = re.search(r"(\d+)", txt)
                if m: habitaciones = int(m.group(1))
            elif "baño" in txt or "aseo" in txt:
                m = re.search(r"(\d+)", txt)
                if m: banos = int(m.group(1))
            elif "construid" in txt or "m2" in txt:
                m = re.search(r"(\d+)", txt.replace(".", ""))
                if m: metros = int(m.group(1))
            elif "parcela" in txt or "terreno" in txt:
                m = re.search(r"(\d+)", txt.replace(".", ""))
                if m: metros_parcela = int(m.group(1))

        # ESTADO - CORRIGIDO: usar el estado capturado desde el listado
        estado = _estados_fincasseminari.get(url, None)
        vendido = False
        if estado:
            if 'VENDIDO' in estado or 'RESERVADO' in estado:
                vendido = True

        # FLAGS
        flags = detectar_flags(texto_completo)
        piscina, garaje, ascensor, vistas_mar, alquiler = (
            flags["piscina"], flags["garaje"], flags["ascensor"], flags["vistas_mar"], flags["alquiler"]
        )

        # GALERÍA
        galeria = []
        vistos = set()
        for img in soup.select(".slideshow img, .slideshow-nav img, img[src*='inmuebles']"):
            if img.has_attr("src"):
                src = urljoin(url, img["src"])
                if not any(x in src.lower() for x in ["logo","icon","banner"]) and src not in vistos:
                    galeria.append(src)
                    vistos.add(src)
        imagen_destacada = galeria[0] if galeria else ""

        # CREAR PROPIEDAD
        tipo = detectar_tipo(titulo)
        return crear_propiedad_estandar(
            referencia=referencia,
            titulo=titulo,
            ubicacion=ubicacion,
            precio=precio,
            metros=metros,
            metros_parcela=metros_parcela,
            habitaciones=habitaciones,
            banos=banos,
            tipo=tipo,
            estado=estado,
            piscina=piscina,
            garaje=garaje,
            ascensor=ascensor,
            vistas_mar=vistas_mar,
            vendido=vendido,
            alquiler=alquiler,
            url_detalle=url,
            inmobiliaria="Fincas Seminari",
            imagen_destacada=imagen_destacada,
            galeria=galeria
        )
    except Exception as e:
        print(f"Error scrapeando Fincas Seminari {url}: {e}")
        return None

def obtener_urls_inmocampsbosch(max_paginas=5):
    """Obtener todas las URLs de inmocampsbosch.com guardando estado"""
    base_url = "https://inmocampsbosch.com/venta.php"
    urls_propiedades = []

    try:
        r = SESSION.get(base_url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, "html.parser")

        items = soup.select("div.single-feature")
        for item in items:
            enlace = item.select_one("a[href*='propiedad.php?id=']")
            estado_tag = item.select_one(".thumb a[href*='propiedad.php?id=']")
            referencia_tag = item.select_one("ul.info-list li")
            referencia = None
            if referencia_tag:
                # tomar todo el texto después del icono
                ref_txt = referencia_tag.get_text(strip=True)
                referencia = ref_txt if ref_txt else None


            estado = None
            if estado_tag:
                estado = estado_tag.get_text(strip=True)

            if enlace and referencia:
                url_detalle = urljoin(base_url, enlace["href"])
                _estados_inmocampsbosch[url_detalle] = estado
                urls_propiedades.append((referencia, url_detalle))

        return list(set(urls_propiedades))
    except Exception as e:
        print(f"Error obteniendo URLs de inmocampsbosch: {e}")
        return []

def scrape_inmocampsbosch_detalle(url, referencia=None):
    """Scraper específico para una propiedad de inmocampsbosch.com"""
    try:
        r = SESSION.get(url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, "html.parser")
        for tag in soup(["header","footer"]):
            tag.decompose()

        texto_completo = soup.get_text(" ", strip=True)

        # TÍTULO
        titulo = None
        h3 = soup.select_one(".property-details-slider-info h3")
        if h3:
            titulo = h3.get_text(strip=True)

        # PRECIO
        precio = None
        h4 = soup.select_one(".property-details-slider-info h4")
        if h4:
            txt = re.sub(r"[^\d]", "", h4.get_text(strip=True))
            if txt.isdigit():
                precio = int(txt)

        # UBICACIÓN
        caracteristicas = {}
        for media in soup.select(".single-floor-list .media-body"):
            key_el = media.select_one("h6")
            val_el = media.select_one("p")
            if key_el and val_el:
                key = key_el.get_text(strip=True).upper()
                val = val_el.get_text(" ", strip=True)
                caracteristicas[key] = val.strip()

        ubicacion    = estandarizar_ubicacion(caracteristicas.get("ZONA"))

        habitaciones = None
        if caracteristicas.get("HABITACIONES") and caracteristicas["HABITACIONES"].isdigit():
            habitaciones = int(caracteristicas["HABITACIONES"])

        banos = None
        if caracteristicas.get("BAÑOS") and caracteristicas["BAÑOS"].isdigit():
            banos = int(caracteristicas["BAÑOS"])

        metros = None
        if caracteristicas.get("SUPERFICIE"):
            m = re.search(r"\d+", caracteristicas["SUPERFICIE"])
            if m:
                metros = int(m.group())

        metros_parcela = None
        if caracteristicas.get("PARCELA"):
            m = re.search(r"\d+", caracteristicas["PARCELA"])
            if m:
                metros_parcela = int(m.group())

        # ESTADO (desde listado)
        estado = _estados_inmocampsbosch.get(url)
        vendido = False
        if estado:
            estado_low = estado.lower()
            if "vendido" in estado_low or "reservado" in estado_low:
                vendido = True
                estado = "VENDIDO"

        # FLAGS
        flags = detectar_flags(texto_completo.upper())
        piscina, garaje, ascensor, vistas_mar, alquiler = (
            flags["piscina"], flags["garaje"], flags["ascensor"], flags["vistas_mar"], flags["alquiler"]
        )

        alquiler = False
        # GALERÍA
        galeria = []
        for img in soup.select(".property-details-slider img, .owl-carousel img"):
            if img.has_attr("src"):
                src = urljoin(url, img["src"])
                if not any(x in src.lower() for x in ["logo","icon","banner"]):
                    if src not in galeria:
                        galeria.append(src)
        imagen_destacada = galeria[0] if galeria else ""

        # CREAR PROPIEDAD
        tipo = detectar_tipo(titulo)
        return crear_propiedad_estandar(
            referencia=referencia,
            titulo=titulo,
            ubicacion=ubicacion,
            precio=precio,
            metros=metros,
            metros_parcela=metros_parcela,
            habitaciones=habitaciones,
            banos=banos,
            tipo=tipo,
            estado=estado,
            piscina=piscina,
            garaje=garaje,
            ascensor=ascensor,
            vistas_mar=vistas_mar,
            vendido=vendido,
            alquiler=alquiler,
            url_detalle=url,
            inmobiliaria="Inmobiliaria Camps Bosch",
            imagen_destacada=imagen_destacada,
            galeria=galeria
        )
    except Exception as e:
        print(f"Error scrapeando inmocampsbosch {url}: {e}")
        return None

def obtener_urls_portalmenorca(max_paginas=20):
    """Obtener todas las URLs de portalmenorca.com recorriendo paginación"""
    base_url = "https://www.portalmenorca.com/es/comprar?pag={}"
    urls_propiedades = []

    for nump in range(1, max_paginas+1):
        url_listado = base_url.format(nump)
        try:
            r = SESSION.get(url_listado, headers=HEADERS, timeout=30)
            r.raise_for_status()
            soup = BeautifulSoup(r.text, "html.parser")

            items = soup.select("div.real-estate-item")
            if not items:
                break  # no más resultados → parar

            for item in items:
                enlace = item.select_one("a[href*='/es/']")
                precio_tag = item.select_one(".real-estate-item-price span")

                referencia = None
                url_detalle = None

                if enlace:
                    href = enlace.get("href")
                    url_detalle = urljoin(url_listado, href)

                if precio_tag:
                    txt = precio_tag.get_text(strip=True)
                    m = re.search(r"REF[: ]?(.+)", txt, re.I)
                    if m:
                        referencia = m.group(1).strip()

                if url_detalle and referencia:
                    urls_propiedades.append((referencia, url_detalle))

            time.sleep(1)

        except Exception as e:
            print(f"Error en página {nump}: {e}")
            break

    # eliminar duplicados
    return list(set(urls_propiedades))

def scrape_portalmenorca_detalle(url, referencia=None):
    """Scraper para un anuncio de portalmenorca.com"""
    try:
        r = SESSION.get(url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, "html.parser")
        for tag in soup(["header", "footer"]):
            tag.decompose()

        texto_completo = soup.get_text(" ", strip=True)

        # Estado
        estado = None
        vendido = False
        estado_tag = soup.select_one(".fslider .label.badge")
        if estado_tag:
            estado_txt = estado_tag.get_text(strip=True).upper()
            if "VENDIDO" in estado_txt or "RESERVADO" in estado_txt:
                estado = "VENDIDO"
                vendido = True

        # Referencia
        if not referencia:
            ref_tag = soup.find("h5", string=re.compile("REF", re.I))
            if ref_tag:
                ref_txt = ref_tag.get_text(strip=True)
                m = re.search(r"REF[: ]?(.+)", ref_txt, re.I)
                if m:
                    referencia = m.group(1).strip()

        # Título
        titulo = None
        h1 = soup.select_one("h1")
        if h1:
            titulo = h1.get_text(strip=True)

        # Precio
        precio = None
        h3_precio = soup.select_one("h3")
        if h3_precio:
            precio_txt = h3_precio.get_text(strip=True)
            m = re.search(r"([\d\.]+)", precio_txt.replace(".", ""))
            if m:
                try:
                    precio = int(m.group(1).replace(".", ""))
                except:
                    precio = None

        # Tipo
        tipo = None
        tipo_tag = soup.find("i", class_="icon-realestate-incision-plan")
        if tipo_tag:
            h5 = tipo_tag.find_next("h5")
            if h5:
                tipo = h5.get_text(strip=True)

        # Ubicación
        ubicacion = None
        ubic_tag = soup.find("i", class_="icon-realestate-map")
        if ubic_tag:
            h5 = ubic_tag.find_next("h5")
            if h5:
                ubicacion_raw = h5.get_text(" ", strip=True)
                if ubicacion_raw:
                    # separar por coma o punto y coma
                    partes = re.split(r"[;,]", ubicacion_raw)
                    # limpiar espacios, descartar vacíos y quitar duplicados manteniendo orden
                    seen = set()
                    partes_unicas = []
                    for p in partes:
                        clean = p.strip()
                        if clean and clean not in seen:
                            partes_unicas.append(clean)
                            seen.add(clean)
                    ubicacion = "; ".join(partes_unicas)

        if ubicacion:
            ubicacion = estandarizar_ubicacion(ubicacion)

        # Metros, habitaciones, baños
        metros = habitaciones = banos = metros_parcela = None
        metros_tag = soup.find("i", class_="icon-realestate-plan2")
        if metros_tag:
            h5 = metros_tag.find_next("h5")
            if h5:
                m = re.search(r"(\d+)", h5.get_text())
                if m: metros = int(m.group(1))

        habs_tag = soup.find("i", class_="icon-realestate-bed")
        if habs_tag:
            h5 = habs_tag.find_next("h5")
            if h5:
                m = re.search(r"(\d+)", h5.get_text())
                if m: habitaciones = int(m.group(1))

        banos_tag = soup.find("i", class_="icon-realestate-bathtub")
        if banos_tag:
            h5 = banos_tag.find_next("h5")
            if h5:
                m = re.search(r"(\d+)", h5.get_text())
                if m: banos = int(m.group(1))

        # Parcela (en sección CARACTERÍSTICAS)
        for li in soup.select(".iconlist li"):
            txt = li.get_text(strip=True).upper()
            if "PARCELA" in txt:
                m = re.search(r"(\d+)", txt)
                if m: metros_parcela = int(m.group(1))

        # Flags
        flags = detectar_flags(texto_completo.upper())
        piscina, garaje, ascensor, vistas_mar, alquiler = (
            flags["piscina"],
            flags["garaje"],
            flags["ascensor"],
            flags["vistas_mar"],
            flags["alquiler"],
        )

        # Galería
        galeria = []
        for img in soup.select(".fslider img"):
            if img.has_attr("src"):
                src = img["src"]
                if not any(x in src.lower() for x in ["logo", "icon", "banner"]):
                    if src not in galeria:
                        galeria.append(src)
        imagen_destacada = galeria[0] if galeria else ""

        # Descripción
        descripcion = None
        desc_p = soup.select("h1 + h3 + p")
        if desc_p:
            descripcion = " ".join(p.get_text(" ", strip=True) for p in desc_p)

        # Crear propiedad
        tipo_norm = detectar_tipo(tipo or titulo)
        return crear_propiedad_estandar(
            referencia=referencia,
            titulo=titulo,
            ubicacion=ubicacion,
            precio=precio,
            metros=metros,
            metros_parcela=metros_parcela,
            habitaciones=habitaciones,
            banos=banos,
            tipo=tipo_norm,
            estado=estado,
            piscina=piscina,
            garaje=garaje,
            ascensor=ascensor,
            vistas_mar=vistas_mar,
            vendido=vendido,
            alquiler=alquiler,
            url_detalle=url,
            inmobiliaria="Portal Menorca",
            imagen_destacada=imagen_destacada,
            galeria=galeria,
            descripcion=descripcion,
        )
    except Exception as e:
        print(f"Error scrapeando Portal Menorca {url}: {e}")
        return None

def obtener_urls_vidalmenorca():
    """Obtener todas las URLs de propiedades de Vidal Menorca desde el sitemap"""
    sitemap_url = "https://www.vidalmenorca.com/sitemap.xml"
    try:
        r = SESSION.get(sitemap_url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        root = ET.fromstring(r.content)

        urls_propiedades = []
        url_elements = root.findall(".//{http://www.sitemaps.org/schemas/sitemap/0.9}url")
        for url_element in url_elements:
            loc_element = url_element.find("{http://www.sitemaps.org/schemas/sitemap/0.9}loc")
            if loc_element is not None:
                url = loc_element.text
                if '/propiedades/' in url:
                    # En Vidal Menorca la referencia se extrae en el detalle
                    urls_propiedades.append((None, url))

        return list(set(urls_propiedades))
    except Exception as e:
        print(f"Error obteniendo URLs de Vidal Menorca: {e}")
        return []



def scrape_vidalmenorca_detalle(url, referencia=None):
    """Scraper para un anuncio de Vidal Menorca"""
    try:
        r = SESSION.get(url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, "html.parser")
        for tag in soup(["header", "footer"]):
            tag.decompose()

        # Eliminar div con id="politica_privacidad"
        politica = soup.find("div", id="politica_privacidad")
        if politica:
            politica.decompose()

        texto_completo = soup.get_text(" ", strip=True)

        # Referencia
        if not referencia:
            ref_tag = soup.find("span", class_="text-muted")
            if ref_tag:
                m = re.search(r"Ref\.\s*[:\-]?\s*(\w+)", ref_tag.get_text())
                if m:
                    referencia = m.group(1).strip()

        # Título
        titulo = None
        h2 = soup.select_one(".accommodation-title")
        if h2:
            titulo = h2.get_text(strip=True)

        # Precio
        precio = None
        precio_tag = soup.select_one(".price-number")
        if precio_tag:
            txt = precio_tag.get_text(strip=True)
            num = re.sub(r"[^\d]", "", txt)
            if num.isdigit():
                precio = int(num)

        # Ubicación
        ubicacion = None
        ubic_tag = soup.find("span", class_="fa fa-map-marker")
        if ubic_tag and ubic_tag.parent:
            ubicacion = ubic_tag.parent.get_text(strip=True)
        ubicacion = estandarizar_ubicacion(ubicacion)

        # Características principales
        habitaciones = banos = metros = None
        metros_parcela = None
        for span in soup.select(".banner span.info"):
            txt = span.get_text(" ", strip=True).lower()
            if "m" in txt:
                m = re.search(r"(\d+)", txt)
                if m: metros = int(m.group(1))
            elif "habit" in txt:
                m = re.search(r"(\d+)", txt)
                if m: habitaciones = int(m.group(1))
            elif "baño" in txt:
                m = re.search(r"(\d+)", txt)
                if m: banos = int(m.group(1))

        # Descripción
        descripcion = None
        desc_div = soup.select_one(".description")
        if desc_div:
            descripcion = desc_div.get_text(" ", strip=True)

        # Galería
        galeria = []
        for img in soup.select(".media-gallery img"):
            if img.has_attr("src"):
                src = urljoin(url, img["src"])
                if not any(x in src.lower() for x in ["logo", "icon", "banner"]):
                    if src not in galeria:
                        galeria.append(src)
        imagen_destacada = galeria[0] if galeria else ""

        # Estado
        estado = None
        vendido = False
        if "vendido" in texto_completo.lower() or "reservado" in texto_completo.lower():
            estado = "VENDIDO"
            vendido = True

        # Flags
        flags = detectar_flags(texto_completo.upper())
        piscina, garaje, ascensor, vistas_mar, alquiler = (
            flags["piscina"],
            flags["garaje"],
            flags["ascensor"],
            flags["vistas_mar"],
            flags["alquiler"],
        )

        tipo = detectar_tipo(titulo)

        return crear_propiedad_estandar(
            referencia=referencia,
            titulo=titulo,
            ubicacion=ubicacion,
            precio=precio,
            metros=metros,
            metros_parcela=metros_parcela,
            habitaciones=habitaciones,
            banos=banos,
            tipo=tipo,
            estado=estado,
            piscina=piscina,
            garaje=garaje,
            ascensor=ascensor,
            vistas_mar=vistas_mar,
            vendido=vendido,
            alquiler=alquiler,
            url_detalle=url,
            inmobiliaria="Vidal Menorca",
            imagen_destacada=imagen_destacada,
            galeria=galeria,
            descripcion=descripcion,
        )
    except Exception as e:
        print(f"Error scrapeando Vidal Menorca {url}: {e}")
        return None

def obtener_urls_menorcasa(max_paginas=30):
    """Obtener las URLs de propiedades en venta de Menorcasa desde su buscador (paginado)"""
    base = "https://menorcasa.com/es/buscador-de-propiedades/"
    urls_propiedades, vistos = [], set()
    for pagina in range(1, max_paginas + 1):
        url_pagina = base if pagina == 1 else f"{base}page/{pagina}/"
        try:
            r = SESSION.get(url_pagina, headers=HEADERS, timeout=30)
            if r.status_code == 404:
                break
            r.raise_for_status()
        except Exception as e:
            print(f"Error obteniendo URLs de Menorcasa (página {pagina}): {e}")
            break
        soup = BeautifulSoup(r.text, "html.parser")
        nuevas = 0
        for a in soup.select("a[href*='/es/property/']"):
            url = a["href"].split("#")[0].split("?")[0]
            if url not in vistos:
                vistos.add(url)
                urls_propiedades.append((None, url))  # referencia se extrae en el detalle
                nuevas += 1
        if nuevas == 0:
            break
        time.sleep(1)
    return urls_propiedades


def scrape_menorcasa_detalle(url, referencia=None):
    """Scraper específico para un detalle de propiedad en Menorcasa"""
    try:
        r = SESSION.get(url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, "html.parser")
        for selector in ["header", "footer", "section.rh_property__similar_properties"]:
            for tag in soup.select(selector):
                tag.decompose()

        # Referencia
        ref_tag = soup.select_one(".rh_property__id .id")
        if ref_tag:
            referencia = ref_tag.get_text(strip=True)

        # Título
        titulo = None
        h1 = soup.select_one("h1.rh_page__title")
        if h1:
            titulo = h1.get_text(strip=True)

        # Precio
        precio = None
        precio_tag = soup.select_one(".rh_page__property_price .price")
        if precio_tag:
            raw_precio = precio_tag.get_text(strip=True)
            # Eliminar símbolo de euro, espacios, puntos y comas
            raw_precio = raw_precio.replace("€", "").replace(".", "").replace(",", "").strip()
            if raw_precio.isdigit():
                precio = int(raw_precio)


        # Estado (vendida / reservada)
        estado = None
        vendido = False

        # Solo las etiquetas de la propia ficha (junto a la referencia), no las de propiedades similares
        labels = [lbl.get_text(strip=True).upper() for lbl in soup.select(".rh_property__id .rh_label__wrap")]

        if any("RESERVAD" in l for l in labels):
            estado = "RESERVADO"
            vendido = True
        elif any("VENDID" in l for l in labels):
            estado = "VENDIDO"
            vendido = True
        elif any("EXCLUSIVA" in l for l in labels):
            estado = "EXCLUSIVA"

        # Ubicación (breadcrumbs)
        ubicacion = None
        breadcrumb = soup.select_one("#breadcrumbs")
        if breadcrumb:
            partes = [a.get_text(strip=True) for a in breadcrumb.select("a")]
            ubicacion = "; ".join(dict.fromkeys(partes[2:]))  # quitar duplicados y primeros genéricos
            ubicacion = estandarizar_ubicacion(ubicacion)

        # Características
        habitaciones = None
        banos = None
        metros = None
        metros_parcela = None

        hab = soup.select_one(".prop_bedrooms .figure")
        if hab: habitaciones = int(hab.get_text(strip=True))

        ban = soup.select_one(".prop_bathrooms .figure")
        if ban: banos = int(ban.get_text(strip=True))

        area = soup.select_one(".prop_area .figure")
        if area: metros = int(re.sub(r"\D", "", area.get_text(strip=True)))

        lot = soup.select_one(".prop_lot_size .figure")
        if lot: metros_parcela = int(re.sub(r"\D", "", lot.get_text(strip=True)))

        # Descripción
        descripcion = None
        desc_tag = soup.select_one("#the_content")
        if desc_tag:
            descripcion = limpiar_texto(desc_tag.get_text(" ", strip=True))

        # Imágenes
        imagenes = []
        for img_tag in soup.select("a.slider-img"):
            if img_tag.has_attr("href"):
                imagenes.append(img_tag["href"])

        imagen_destacada = imagenes[0] if imagenes else ""

         # Flags (título + descripción, sin las tarjetas de propiedades similares)
        flags = detectar_flags(f"{titulo or ''} {descripcion or ''}".upper())
        piscina, garaje, ascensor, vistas_mar, alquiler = (
            flags["piscina"],
            flags["garaje"],
            flags["ascensor"],
            flags["vistas_mar"],
            flags["alquiler"],
        )

         # CREAR PROPIEDAD
        tipo = detectar_tipo(titulo)
        return crear_propiedad_estandar(
            referencia=referencia,
            titulo=titulo,
            ubicacion=ubicacion,
            precio=precio,
            metros=metros,
            metros_parcela=metros_parcela,
            habitaciones=habitaciones,
            banos=banos,
            tipo=tipo,
            estado=estado,
            piscina=piscina,
            garaje=garaje,
            ascensor=ascensor,
            vistas_mar=vistas_mar,
            vendido=vendido,
            alquiler=alquiler,
            url_detalle=url,
            inmobiliaria="Menorcasa",
            imagen_destacada=imagen_destacada,
            galeria=imagenes,
            descripcion=descripcion,
        )

    except Exception as e:
        print(f"Error scrapeando Menorcasa {url}: {e}")
        return None

def obtener_urls_saimmobiliaria():
    """Obtener todas las URLs de propiedades de SA Inmobiliaria desde el sitemap"""
    sitemap_url = "https://www.saimmobiliaria.com/sitemap-es-es.xml"
    try:
        r = SESSION.get(sitemap_url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        root = ET.fromstring(r.content)

        ns = {"sm": "http://www.sitemaps.org/schemas/sitemap/0.9"}
        urls_propiedades = []
        for url_tag in root.findall("sm:url", ns):
            loc = url_tag.find("sm:loc", ns)
            if loc is None:
                continue
            url = loc.text.strip()
            if "/inmueble/" not in url:
                continue

            referencia = url.split("/")[-1] if not url.endswith("/") else url.split("/")[-2]
            if not referencia:
                referencia = "unknown"
            urls_propiedades.append((referencia, url))

        return urls_propiedades
    except Exception as e:
        print(f"Error obteniendo URLs de SA Inmobiliaria: {e}")
        return []

def scrape_saimmobiliaria_detalle(url, referencia=None):
    """Scraper específico para una propiedad de saimmobiliaria.com usando JSON-LD"""
    try:
        r = SESSION.get(url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, "html.parser")

        # Buscar bloques JSON-LD
        json_blocks = soup.find_all("script", type="application/ld+json")
        data_listing = data_breadcrumb = None

        for block in json_blocks:
            try:
                data = json.loads(block.string)
            except Exception:
                continue
            if not isinstance(data, dict):
                continue
            if data.get("@type") == "RealEstateListing":
                data_listing = data
            elif data.get("@type") == "BreadcrumbList":
                data_breadcrumb = data

        if not data_listing:
            print(f"No JSON-LD RealEstateListing en {url}")
            return None

        # ======================
        # REFERENCIA
        # ======================
        if not referencia:
            match = re.search(r"/(\d+)$", data_listing.get("url", ""))
            if match:
                referencia = match.group(1)

        # ======================
        # TÍTULO, DESCRIPCIÓN
        # ======================
        titulo = data_listing.get("name")
        descripcion = data_listing.get("description")

        # ======================
        # PRECIO
        # ======================
        precio = None
        offers = data_listing.get("offers", {})
        if isinstance(offers, dict):
            precio_str = offers.get("price")
            if precio_str and str(precio_str).isdigit():
                precio = int(precio_str)

        # ======================
        # UBICACIÓN (breadcrumb)
        # ======================
        ubicacion = None
        if data_breadcrumb:
            items = [it.get("name") for it in data_breadcrumb.get("itemListElement", []) if it.get("name")]
            if len(items) > 2:
                items = items[2:-1]  # quitamos niveles genéricos + el último (título)
            seen, ubic_list = set(), []
            for it in items:
                if it not in seen:
                    ubic_list.append(it)
                    seen.add(it)
            if ubic_list:
                ubicacion = "; ".join(ubic_list)
                ubicacion = estandarizar_ubicacion(ubicacion)

        # ======================
        # CARACTERÍSTICAS (extraer de descripción)
        # ======================
        habitaciones = banos = metros = metros_parcela = None
        if descripcion:
            desc = descripcion.lower()
            m = re.search(r"(\d+)\s*(?:habitaciones?|dormitorios?)", desc)
            if m: habitaciones = int(m.group(1))
            m = re.search(r"(\d+)\s*(?:baños?|aseos?)", desc)
            if m: banos = int(m.group(1))
            m = re.search(r"(\d[\d\.,]*)\s*(?:m2|m²)", desc)
            if m:
                try: metros = int(m.group(1).replace(".","").replace(",",""))
                except: pass
            m = re.search(r"(\d[\d\.,]*)\s*(?:m2|m²).*(parcela|solar|terreno)", desc)
            if m:
                try: metros_parcela = int(m.group(1).replace(".","").replace(",",""))
                except: pass

        # ======================
        # IMÁGENES
        # ======================
        galeria = []
        if data_listing.get("image"):
            if isinstance(data_listing["image"], list):
                galeria = data_listing["image"]
            else:
                galeria = [data_listing["image"]]
        imagen_destacada = galeria[0] if galeria else None

        # ======================
        # ESTADO
        # ======================
        estado, vendido = None, False
        for st in soup.select(".stickerRender .stickerText"):
            txt = st.get_text(strip=True).upper()
            if "VENDIDO" in txt or "RESERVADO" in txt or "ALQUILADO" in txt:
                estado, vendido = "VENDIDO", True
            elif txt not in ["DISPONIBLE", "NOVEDAD"]:
                estado = txt

        # ======================
        # FLAGS
        # ======================
        extra_txt = []

        # añadir título
        if titulo:
            extra_txt.append(titulo)

        # añadir descripción
        if descripcion:
            extra_txt.append(descripcion)

        # añadir breadcrumb
        if data_breadcrumb:
            nombres = [it.get("name", "") for it in data_breadcrumb.get("itemListElement", [])]
            extra_txt.extend(nombres)

        # añadir todo el texto visible
        extra_txt.append(soup.get_text())

        # crear el string final
        texto_flags = " ".join(extra_txt).upper()

        # pasar a detectar_flags
        flags = detectar_flags(texto_flags)
        piscina, garaje, ascensor, vistas_mar, alquiler = (
            flags["piscina"], flags["garaje"], flags["ascensor"], flags["vistas_mar"], flags["alquiler"]
        )

        # CREAR PROPIEDAD
        tipo = detectar_tipo(titulo)
        return crear_propiedad_estandar(
            referencia=referencia,
            titulo=titulo,
            ubicacion=ubicacion,
            precio=precio,
            metros=metros,
            metros_parcela=metros_parcela,
            habitaciones=habitaciones,
            banos=banos,
            tipo=tipo,
            estado=estado,
            piscina=piscina,
            garaje=garaje,
            ascensor=ascensor,
            vistas_mar=vistas_mar,
            vendido=vendido,
            alquiler=alquiler,
            url_detalle=url,
            inmobiliaria="SA Inmobiliaria",
            imagen_destacada=imagen_destacada,
            galeria=galeria
        )
    except Exception as e:
        print(f"Error scrapeando SA Inmobiliaria {url}: {e}")
        return None

def obtener_urls_3villas():
    """Obtener todas las URLs de propiedades de 3Villas desde el sitemap (solo /inmueble/)."""
    sitemap_url = "https://www.3villas.es/sitemap-es-es.xml"
    try:
        r = SESSION.get(sitemap_url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        root = ET.fromstring(r.content)

        ns = {"sm": "http://www.sitemaps.org/schemas/sitemap/0.9"}
        urls_propiedades = []
        for url_tag in root.findall("sm:url", ns):
            loc = url_tag.find("sm:loc", ns)
            if loc is None:
                continue
            url = loc.text.strip()
            if "/inmueble/" not in url:
                continue

            # referencia = el último segmento de la URL
            referencia = url.split("/")[-1] if not url.endswith("/") else url.split("/")[-2]
            if not referencia:
                referencia = "unknown"

            urls_propiedades.append((referencia, url))

        # eliminar duplicados por si acaso
        return list(set(urls_propiedades))
    except Exception as e:
        print(f"Error obteniendo URLs de 3Villas: {e}")
        return []


def scrape_3villas_detalle(url, referencia=None):
    """Scraper específico para una propiedad de 3villas.es usando JSON-LD (misma plataforma que SA Inmobiliaria)."""
    try:
        r = SESSION.get(url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, "html.parser")

        # Buscar bloques JSON-LD
        json_blocks = soup.find_all("script", type="application/ld+json")
        data_listing = data_breadcrumb = None

        for block in json_blocks:
            try:
                data = json.loads(block.string)
            except Exception:
                continue
            if not isinstance(data, dict):
                continue
            if data.get("@type") == "RealEstateListing":
                data_listing = data
            elif data.get("@type") == "BreadcrumbList":
                data_breadcrumb = data

        if not data_listing:
            print(f"No JSON-LD RealEstateListing en {url}")
            return None

        # ======================
        # REFERENCIA
        # ======================
        if not referencia:
            match = re.search(r"/(\d+)$", data_listing.get("url", "") or url)
            if match:
                referencia = match.group(1)

        # ======================
        # TÍTULO, DESCRIPCIÓN
        # ======================
        titulo = data_listing.get("name")
        descripcion = data_listing.get("description")

        # ======================
        # PRECIO
        # ======================
        precio = None
        offers = data_listing.get("offers", {})
        if isinstance(offers, dict):
            precio_str = offers.get("price")
            if precio_str and str(precio_str).isdigit():
                precio = int(precio_str)

        # ======================
        # UBICACIÓN (breadcrumb)
        # ======================
        ubicacion = None
        if data_breadcrumb:
            items = [it.get("name") for it in data_breadcrumb.get("itemListElement", []) if it.get("name")]
            # quitar niveles genéricos y el último (título)
            if len(items) > 2:
                items = items[2:-1]
            seen, ubic_list = set(), []
            for it in items:
                if it and it not in seen:
                    ubic_list.append(it)
                    seen.add(it)
            if ubic_list:
                ubicacion = "; ".join(ubic_list)
                ubicacion = estandarizar_ubicacion(ubicacion)

        # ======================
        # CARACTERÍSTICAS (desde descripción si aparecen)
        # ======================
        habitaciones = banos = metros = metros_parcela = None
        if descripcion:
            desc = descripcion.lower()
            m = re.search(r"(\d+)\s*(?:habitaciones?|dormitorios?)", desc)
            if m: habitaciones = int(m.group(1))
            m = re.search(r"(\d+)\s*(?:baños?|aseos?)", desc)
            if m: banos = int(m.group(1))
            m = re.search(r"(\d[\d\.,]*)\s*(?:m2|m²)", desc)
            if m:
                try:
                    metros = int(m.group(1).replace(".", "").replace(",", ""))
                except:
                    pass
            m = re.search(r"(\d[\d\.,]*)\s*(?:m2|m²).*(parcela|solar|terreno)", desc)
            if m:
                try:
                    metros_parcela = int(m.group(1).replace(".", "").replace(",", ""))
                except:
                    pass

        # ======================
        # ESTADO / FLAGS / GALERÍA
        # ======================
        texto_upper = soup.get_text(" ", strip=True).upper()
        flags = detectar_flags(texto_upper)
        piscina = flags["piscina"]
        garaje = flags["garaje"]
        ascensor = flags["ascensor"]
        vistas_mar = flags["vistas_mar"]
        alquiler = flags["alquiler"]

        # Galería (si la plataforma incluye array de imágenes en el JSON-LD)
        galeria = []
        images = data_listing.get("image")
        if images:
            galeria = images if isinstance(images, list) else [images]
        imagen_destacada = galeria[0] if galeria else ""

        # Estado (vendido/reservado a partir de stickers/texto)
        estado = None
        vendido = False
        if "VENDIDO" in texto_upper or "RESERVADO" in texto_upper:
            estado, vendido = "VENDIDO", True

        # Tipo
        tipo = detectar_tipo(titulo)

        # Crear propiedad estandarizada
        return crear_propiedad_estandar(
            referencia=referencia,
            titulo=titulo,
            ubicacion=ubicacion,
            precio=precio,
            metros=metros,
            metros_parcela=metros_parcela,
            habitaciones=habitaciones,
            banos=banos,
            tipo=tipo,
            estado=estado,
            piscina=piscina,
            garaje=garaje,
            ascensor=ascensor,
            vistas_mar=vistas_mar,
            vendido=vendido,
            alquiler=alquiler if alquiler and (precio is None or precio <= 6000) else False,
            url_detalle=url,
            inmobiliaria="3Villas",
            imagen_destacada=imagen_destacada,
            galeria=galeria
        )
    except Exception as e:
        print(f"Error scrapeando 3Villas {url}: {e}")
        return None


def scrape_finquesfuguet_listado():
    url_listado = "https://www.finquesinmofuguet.com/propiedades-venta.php"
    try:
        r = SESSION.get(url_listado, headers=HEADERS, timeout=30)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, 'html.parser')

        propiedades = []
        items = soup.select("div.property-block")
        total = len(items)

        for idx, item in enumerate(items, 1):
            # URL y referencia
            enlace = item.select_one("a[href*='propiedad-v.php']")
            if not enlace:
                continue
            href = enlace['href']
            url_detalle = urljoin(url_listado, href)

            h3 = item.select_one("h3 a")
            referencia = None
            titulo = None
            if h3:
                texto_h3 = h3.get_text(strip=True)
                m = re.search(r'REF[:\s]*(\d+)', texto_h3, re.IGNORECASE)
                if m:
                    referencia = m.group(1)
                # Título es el texto después del REF y salto de línea
                titulo = re.sub(r'REF[:\s]*\d+', '', texto_h3).strip()

            if not referencia:
                m = re.search(r'id=(\d+)', href)
                if m:
                    referencia = m.group(1)

           # Estado
            estado_tag = item.select_one("div.sale")
            estado = estado_tag.get_text(strip=True).upper() if estado_tag else None
            
            # Ignorar estados descriptivos
            ESTADOS_IGNORAR = {'ESPECTACULAR', 'BUEN ESTADO'}
            if estado in ESTADOS_IGNORAR:
                estado = None
            
            vendido = bool(estado and ('VENDIDO' in estado or 'RESERVADO' in estado))

            # Precio
            precio = None
            precio_tag = item.select_one("div.price")
            if precio_tag:
                precio_txt = re.sub(r'[^\d]', '', precio_tag.get_text(strip=True))
                if precio_txt.isdigit():
                    precio = int(precio_txt)

            # Ubicación
            ubicacion = None
            ubic_tag = item.select_one("div.location")
            if ubic_tag:
                ubicacion = estandarizar_ubicacion(ubic_tag.get_text(strip=True))

            # Habitaciones
            habitaciones = None
            hab = item.select_one("span.flaticon-bed-1")
            if hab:
                m = re.search(r'\d+', hab.parent.get_text())
                if m: habitaciones = int(m.group())

            # Baños
            banos = None
            ban = item.select_one("span.flaticon-bathtube-with-shower")
            if ban:
                m = re.search(r'\d+', ban.parent.get_text())
                if m: banos = int(m.group())

            # Metros
            metros = None
            met = item.select_one("span.flaticon-squares")
            if met:
                m = re.search(r'\d+', met.parent.get_text())
                if m: metros = int(m.group())

            # Imagen
            imagen_destacada = ''
            img_tag = item.select_one("div.image img")
            if img_tag:
                src = img_tag.get('src', '')
                if src:
                    imagen_destacada = urljoin(url_listado, src)

            # Flags desde título
            flags = detectar_flags((titulo or '').upper())
            piscina, garaje, ascensor, vistas_mar, alquiler = (
                flags['piscina'], flags['garaje'], flags['ascensor'], flags['vistas_mar'], flags['alquiler']
            )
            alquiler = False

            tipo = detectar_tipo(titulo)
            data = crear_propiedad_estandar(
                referencia=referencia,
                titulo=titulo,
                ubicacion=ubicacion,
                precio=precio,
                metros=metros,
                metros_parcela=None,
                habitaciones=habitaciones,
                banos=banos,
                tipo=tipo,
                estado=estado,
                piscina=piscina,
                garaje=garaje,
                ascensor=ascensor,
                vistas_mar=vistas_mar,
                vendido=vendido,
                alquiler=alquiler,
                url_detalle=url_detalle,
                inmobiliaria='Finques Fuguet',
                imagen_destacada=imagen_destacada,
                galeria=[imagen_destacada] if imagen_destacada else []
            )
            propiedades.append(data)
            print(f"  ✔ {idx}/{total} ref {referencia} -> {titulo}")

        return propiedades
    except Exception as e:
        print(f"Error scrapeando listado Finques Fuguet: {e}")
        return []


def _ubicacion_menorca(raw):
    """Normaliza variantes que estandarizar_ubicacion no cubre ('Maó/Mahón', 'Ciudadela de Menorca'...)."""
    if not raw:
        return None
    t = raw.strip()
    low = t.lower()
    if 'mahón' in low or 'mahon' in low or low.startswith('maó') or low == 'mao':
        t = 'Maó'
    elif 'ciudadela' in low or 'ciutadella' in low:
        t = 'Ciutadella'
    elif low in ('mercadal', 'es mercadal'):
        t = 'Es Mercadal'
    elif low in ('migjorn gran', 'es migjorn gran'):
        t = 'Es Migjorn Gran'
    return estandarizar_ubicacion(t)


def _estado_desde_texto(txt):
    """Devuelve ('VENDIDO'|'RESERVADO'|'', vendido) a partir del texto/clase de un badge concreto."""
    t = (txt or '').upper()
    if 'VENDID' in t or 'SOLD' in t:
        return 'VENDIDO', True
    if 'RESERVAD' in t or 'RESERVED' in t:
        return 'RESERVADO', True
    return '', False


# ===== FINCAS MENORQUINAS (WordPress + inmocms) =====

FINCASMENORQUINAS_BUSCADOR = "https://fincasmenorquinas.com/buscador"


def obtener_urls_fincasmenorquinas(max_paginas=20):
    """URLs de inmuebles en VENTA de Fincas Menorquinas.
    El buscador acepta ?opcion=venta&page=N; hoy devuelve todo en una página (si page se ignora,
    se repiten las mismas fichas y el bucle se corta)."""
    urls, vistos = [], set()
    for page in range(max_paginas):
        try:
            r = SESSION.get(FINCASMENORQUINAS_BUSCADOR, params={"opcion": "venta", "page": page},
                             headers=HEADERS, timeout=30)
            r.raise_for_status()
        except Exception as e:
            print(f"Error obteniendo listado Fincas Menorquinas (page={page}): {e}")
            break
        soup = BeautifulSoup(r.text, "lxml")
        nuevas = 0
        for a in soup.select("a.inmueble-horizontal-card[href*='/inmueble/']"):
            url = urljoin(FINCASMENORQUINAS_BUSCADOR, a["href"].strip())
            if url in vistos:
                continue
            # Solo venta (el filtro ya lo aplica, se comprueba por si acaso)
            op = a.select_one(".inmueble-horizontal-card-content-top-price-text")
            if op and 'VENTA' not in op.get_text(strip=True).upper():
                continue
            vistos.add(url)
            m = re.search(r'-(\d+)/?$', url)
            referencia = f"FM-{m.group(1)}" if m else url.rstrip('/').split('/')[-1][:20]
            urls.append((referencia, url))
            nuevas += 1
        if nuevas == 0:
            break
        time.sleep(1)
    print(f"  Fincas Menorquinas: {len(urls)} URLs")
    return urls


def scrape_fincasmenorquinas_detalle(url, referencia=None):
    """Ficha de fincasmenorquinas.com/inmueble/... (plugin inmocms)."""
    try:
        r = SESSION.get(url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, "lxml")

        bloque = soup.select_one(".inmocms-inmueble-block") or soup

        # Referencia real de la agencia ("REF.: #E43")
        ref_el = bloque.select_one(".inmocms-contact-info-reference, .inmocms-agente-reference")
        if ref_el:
            m = re.search(r'#\s*([\w-]+)', ref_el.get_text(" ", strip=True))
            if m:
                referencia = m.group(1)

        titulo_el = bloque.select_one(".inmueble-title")
        titulo = re.sub(r'\s+', ' ', titulo_el.get_text("")).strip() if titulo_el else None

        loc_el = bloque.select_one(".inmueble-location")
        ubicacion = _ubicacion_menorca(loc_el.get_text(" ", strip=True) if loc_el else None)

        precio_el = bloque.select_one(".inmocms-price")
        precio = _pm_clean_int(precio_el.get_text(" ", strip=True)) if precio_el else None

        # Características: Habitaciones / Baños / Área / Parcela...
        habitaciones = banos = metros = metros_parcela = None
        for item in bloque.select(".inmocms-caracteristicas-item"):
            t = item.select_one(".inmocms-caracteristicas-item-title")
            v = item.select_one(".inmocms-caracteristicas-item-data-value")
            if not t or not v:
                continue
            clave = t.get_text(strip=True).lower()
            m = re.search(r'\d[\d.]*', v.get_text("", strip=True))
            valor = int(m.group(0).replace('.', '')) if m else None
            if valor is None:
                continue
            if clave.startswith('habita') or clave.startswith('dormit'):
                habitaciones = valor
            elif clave.startswith('baño'):
                banos = valor
            elif clave in ('área', 'area', 'superficie', 'construidos', 'superficie construida'):
                metros = valor
            elif 'parcela' in clave or 'terreno' in clave or 'solar' in clave:
                metros_parcela = valor

        # Estado: badge sobre la foto principal (<div class="inmueble-estado-general big reservado banner">)
        estado, vendido = '', False
        badge = bloque.select_one(".inmocms-poster .inmueble-estado-general")
        if badge:
            estado, vendido = _estado_desde_texto(" ".join(badge.get("class", [])) + " " + badge.get_text(" ", strip=True))

        # Descripción + lista de características (para flags). Se excluye la rejilla de iconos
        # (.inmocms-caracteristicas), que siempre muestra "Piscina" aunque no tenga.
        descripcion = ""
        cont = bloque.select_one(".inmueble-contenido")
        if cont:
            cont = BeautifulSoup(str(cont), "lxml")
            for basura in cont.select(".inmueble-datos, .inmocms-caracteristicas, .inmocms-certificado, "
                                      ".inmocms-inmueble-mapa, style, script"):
                basura.decompose()
            descripcion = cont.get_text(" ", strip=True)
        flags = detectar_flags(f"{titulo or ''} {descripcion}")

        # Galería: array JS fotos_list.push('...') con las fotos a tamaño completo
        galeria = []
        for src in re.findall(r"fotos_list\.push\('([^']+)'\)", r.text):
            if src not in galeria and 'thumbnail_' not in src:
                galeria.append(src)
        if not galeria:
            poster = bloque.select_one(".inmocms-poster")
            m = re.search(r"url\('([^']+)'\)", poster.get("style", "")) if poster else None
            if m:
                galeria.append(m.group(1))
        imagen_destacada = galeria[0] if galeria else ''

        tipo = detectar_tipo(titulo)

        return crear_propiedad_estandar(
            referencia=referencia,
            titulo=titulo,
            ubicacion=ubicacion,
            precio=precio,
            metros=metros,
            metros_parcela=metros_parcela,
            habitaciones=habitaciones,
            banos=banos,
            tipo=tipo,
            estado=estado,
            piscina=flags['piscina'],
            garaje=flags['garaje'],
            ascensor=flags['ascensor'],
            vistas_mar=flags['vistas_mar'],
            vendido=vendido,
            alquiler=False,
            url_detalle=url,
            inmobiliaria='Fincas Menorquinas',
            imagen_destacada=imagen_destacada,
            galeria=galeria,
        )
    except Exception as e:
        print(f"Error scrapeando Fincas Menorquinas {url}: {e}")
        return None


# ===== LUCAS FOX (Menorca, venta, <= 400.000 €) =====

LUCASFOX_LISTADO = "https://www.lucasfox.es/buscar.html"
LUCASFOX_PARAMS = {"classid": "res_sale", "locationid": "5B78C6C2EC", "priceto": "400000", "pagesize": "24"}
LUCASFOX_CRAWL_DELAY = 10  # robots.txt: "Crawl-delay: 10"
_lucasfox_ultima_peticion = [0.0]


def _lucasfox_get(url, **kwargs):
    """GET respetando el Crawl-delay de 10 s de robots.txt de lucasfox.es."""
    espera = LUCASFOX_CRAWL_DELAY - (time.time() - _lucasfox_ultima_peticion[0])
    if espera > 0:
        time.sleep(espera)
    try:
        r = SESSION.get(url, headers=HEADERS, timeout=30, **kwargs)
    finally:
        _lucasfox_ultima_peticion[0] = time.time()
    r.raise_for_status()
    return r


def obtener_urls_lucasfox(max_paginas=30):
    """URLs de Lucas Fox: venta en Menorca con precio <= 400.000 €, recorriendo la paginación."""
    urls, vistos = [], set()
    total_paginas = 1
    page = 1
    while page <= min(total_paginas, max_paginas):
        try:
            r = _lucasfox_get(LUCASFOX_LISTADO, params={**LUCASFOX_PARAMS, "page": page})
        except Exception as e:
            print(f"Error obteniendo listado Lucas Fox (page={page}): {e}")
            break
        soup = BeautifulSoup(r.text, "lxml")

        # "Página <strong>1</strong> de 3"
        status = soup.select_one(".listing-pagination__status")
        if status:
            m = re.search(r'de\s+(\d+)', status.get_text(" ", strip=True))
            if m:
                total_paginas = int(m.group(1))

        nuevas = 0
        for outer in soup.select("ul.property-card-grid .property-card-outer"):
            a = outer.select_one("a.property-card[href]")
            if not a:
                continue
            url = urljoin(LUCASFOX_LISTADO, a["href"].strip())
            if url in vistos:
                continue
            vistos.add(url)
            referencia = (outer.get("data-reference") or url.rstrip('/').split('/')[-1].replace('.html', '')).upper()
            urls.append((referencia, url))
            nuevas += 1
        if nuevas == 0:
            break
        page += 1
    print(f"  Lucas Fox: {len(urls)} URLs ({total_paginas} páginas)")
    return urls


def scrape_lucasfox_detalle(url, referencia=None):
    """Ficha de lucasfox.es/comprar-vivienda/.../menXXXXX.html"""
    try:
        r = _lucasfox_get(url)
        soup = BeautifulSoup(r.text, "lxml")

        # Quitar bloque de inmuebles similares para que no contamine nada
        for card in soup.select(".property-card, .property-card-outer, ul.property-card-grid"):
            card.decompose()

        banner = soup.select_one(".detail-banner__body") or soup

        metas = banner.select_one(".detail-metas")
        if metas:
            ref_el = metas.select_one("span.text-uppercase")
            if ref_el and ref_el.get_text(strip=True):
                referencia = ref_el.get_text(strip=True).upper()
        precio_el = metas.select_one("b") if metas else None
        precio = _pm_clean_int(precio_el.get_text(" ", strip=True)) if precio_el else None
        tipo_txt = " ".join(s.get_text(" ", strip=True) for s in metas.select("span")) if metas else ""

        h1 = banner.select_one("h1")
        titulo = h1.get_text(" ", strip=True) if h1 else None

        # Municipio: último enlace del breadcrumb (España > Islas Baleares > Menorca > Es Castell)
        crumbs = [a.get("title") or a.get_text(strip=True) for a in banner.select("ul.crumb a")]
        municipio = crumbs[-1] if crumbs and crumbs[-1].lower() != 'menorca' else None
        ubicacion = _ubicacion_menorca(municipio)

        habitaciones = banos = metros = metros_parcela = None
        for li in banner.select("ul.key-facts li.key-facts__item"):
            k = li.select_one(".key-facts__key")
            v = li.select_one(".key-facts__value")
            if not k or not v:
                continue
            clave = k.get_text(strip=True).lower()
            m = re.search(r'\d[\d.,]*', v.get_text(strip=True))
            valor = int(re.sub(r'[.,]', '', m.group(0))) if m else None
            if valor is None:
                continue
            if clave.startswith('dormit') or clave.startswith('habita'):
                habitaciones = valor
            elif clave.startswith('baño'):
                banos = valor
            elif clave in ('plano', 'superficie', 'construidos', 'tamaño construido'):
                metros = valor
            elif 'parcela' in clave:
                metros_parcela = valor

        # Estado: <div class="detail-banner-sashes"><span class="sash reserved">Reservado</span>
        estado, vendido = '', False
        for sash in soup.select(".detail-banner__meta .detail-banner-sashes .sash"):
            e, v = _estado_desde_texto(" ".join(sash.get("class", [])) + " " + sash.get_text(" ", strip=True))
            if e == 'VENDIDO' or (e and not estado):
                estado, vendido = e, v

        descripcion = " ".join(d.get_text(" ", strip=True) for d in soup.select(".detail-body__content"))
        flags = detectar_flags(f"{titulo or ''} {descripcion}")

        # Galería: enlaces fancybox "images" (4x3_1600w) de la propia ficha
        galeria = []
        for a in soup.select('a[data-fancybox="images"][href]'):
            src = a["href"].strip()
            if 'images.lucasfox.com/' in src and '/4x3_' in src and src not in galeria:
                galeria.append(src)
        if not galeria:
            img = soup.select_one("img.detail-banner__image")
            if img and img.get("src"):
                galeria.append(img["src"])
        imagen_destacada = galeria[0] if galeria else ''

        tipo = detectar_tipo(titulo) or detectar_tipo(tipo_txt)

        return crear_propiedad_estandar(
            referencia=referencia,
            titulo=titulo,
            ubicacion=ubicacion,
            precio=precio,
            metros=metros,
            metros_parcela=metros_parcela,
            habitaciones=habitaciones,
            banos=banos,
            tipo=tipo,
            estado=estado,
            piscina=flags['piscina'],
            garaje=flags['garaje'],
            ascensor=flags['ascensor'],
            vistas_mar=flags['vistas_mar'],
            vendido=vendido,
            alquiler=False,
            url_detalle=url,
            inmobiliaria='Lucas Fox',
            imagen_destacada=imagen_destacada,
            galeria=galeria,
        )
    except Exception as e:
        print(f"Error scrapeando Lucas Fox {url}: {e}")
        return None


# =====================================================================
# FINCAS CALA (fincascala.com) - WordPress + tema Houzez
# Para pegar en scraper_historico.py (usa HEADERS, detectar_flags,
# detectar_tipo, estandarizar_ubicacion, crear_propiedad_estandar,
# requests, BeautifulSoup, re, time ya importados allí).
#
# - Listado: REST /wp-json/wp/v2/properties (expone taxonomías y
#   property_meta con fave_property_id / fave_property_price).
#   Fallback: property-sitemap.xml.
# - Detalle: HTML de la ficha (precio, etiquetas, detalles, galería)
#   + REST del post (postid) solo para zona/ciudad, que no aparece en el HTML.
# - Vendido/Reservado: SOLO desde el elemento de precio
#   (.property-title-price-wrap .item-price / campo "Precio:" de Detalles)
#   y las etiquetas Houzez de la ficha (.property-labels-wrap).
# =====================================================================

FINCASCALA_BASE = "https://fincascala.com"
FINCASCALA_API = FINCASCALA_BASE + "/wp-json/wp/v2"

# Cache de taxonomías {taxonomia: {id: nombre}}
_fincascala_tax_cache = {}

# Estados Houzez que indican venta (todo lo que no sea solo alquiler)
_FINCASCALA_ESTADOS_ALQUILER = {"ALQUILER", "ALQUILER TURÍSTICO", "ALQUILER TURISTICO", "FOR RENT"}


def _fincascala_taxonomia(tax):
    """Devuelve {id: nombre} de una taxonomía Houzez (property_status, property_city, property_area...)."""
    if tax in _fincascala_tax_cache:
        return _fincascala_tax_cache[tax]
    mapa = {}
    try:
        r = SESSION.get(f"{FINCASCALA_API}/{tax}", params={"per_page": 100, "_fields": "id,name"},
                         headers=HEADERS, timeout=30)
        r.raise_for_status()
        for t in r.json():
            mapa[t["id"]] = BeautifulSoup(t.get("name", ""), "html.parser").get_text().strip()
    except Exception as e:
        print(f"Fincas Cala: no se pudo leer taxonomía {tax}: {e}")
    _fincascala_tax_cache[tax] = mapa
    return mapa


def _fincascala_estado_desde_texto(txt):
    """Normaliza un texto de precio/etiqueta a 'VENDIDO' / 'RESERVADO' / None."""
    if not txt:
        return None
    t = txt.upper()
    if re.search(r"\bVENDID[OA]S?\b|\bVENUD[AE]S?\b|\bVENUTS?\b|\bSOLD\b", t):
        return "VENDIDO"
    if re.search(r"\bRESERVAD[OA]S?\b|\bRESERVAT(?:S|DA|DES)?\b|\bRESERVED\b|\bUNDER OFFER\b", t):
        return "RESERVADO"
    return None


def obtener_urls_fincascala():
    """Lista de (referencia, url) de las propiedades en VENTA de Fincas Cala.
    Excluye las que solo tienen estado de alquiler. Incluye vendidas (se marcan en el detalle)."""
    urls = []
    try:
        estados = _fincascala_taxonomia("property_status")
        pagina, total_paginas = 1, 1
        while pagina <= total_paginas:
            r = SESSION.get(f"{FINCASCALA_API}/properties",
                             params={"per_page": 100, "page": pagina,
                                     "_fields": "id,slug,link,property_status,property_meta"},
                             headers=HEADERS, timeout=30)
            r.raise_for_status()
            total_paginas = int(r.headers.get("X-WP-TotalPages", 1) or 1)
            for p in r.json():
                nombres = {estados.get(i, "").upper() for i in p.get("property_status", [])}
                # Solo alquiler -> fuera. Sin estado o con Compra/Traspaso/etc. -> dentro
                if nombres and nombres <= _FINCASCALA_ESTADOS_ALQUILER:
                    continue
                meta = p.get("property_meta") or {}
                ref = (meta.get("fave_property_id") or [""])[0]
                if not ref:
                    m = re.search(r"ref-(\d+)", p.get("slug", ""))
                    ref = m.group(1) if m else str(p["id"])
                urls.append((str(ref).strip(), p["link"]))
            pagina += 1
            if pagina <= total_paginas:
                time.sleep(1)
    except Exception as e:
        print(f"Fincas Cala: REST falló ({e}), usando sitemap")
        urls = []
        try:
            r = SESSION.get(f"{FINCASCALA_BASE}/property-sitemap.xml", headers=HEADERS, timeout=30)
            r.raise_for_status()
            for loc in re.findall(r"<loc>([^<]+)</loc>", r.text):
                loc = loc.strip()
                if not re.search(r"/propiedades/[^/]+/?$", loc):
                    continue  # descarta /propiedades/ (archivo)
                slug = loc.rstrip("/").split("/")[-1]
                m = re.search(r"ref-(\d+)", slug)
                urls.append((m.group(1) if m else slug, loc))
            # Nota: sin REST no se puede filtrar alquiler aquí; se filtra en el detalle (alquiler=True)
        except Exception as e2:
            print(f"Error obteniendo URLs de Fincas Cala: {e2}")
            return []
    # sin duplicados, manteniendo orden
    vistos, res = set(), []
    for ref, u in urls:
        if u not in vistos:
            vistos.add(u)
            res.append((ref, u))
    return res


def _fincascala_ubicacion(post_id):
    """Zona/ciudad desde la REST (el HTML de la ficha no la muestra)."""
    ciudad = zona = None
    if not post_id:
        return None
    try:
        r = SESSION.get(f"{FINCASCALA_API}/properties/{post_id}",
                         params={"_fields": "property_city,property_area"}, headers=HEADERS, timeout=30)
        r.raise_for_status()
        d = r.json()
        ciudades = _fincascala_taxonomia("property_city")
        areas = _fincascala_taxonomia("property_area")
        if d.get("property_city"):
            ciudad = ciudades.get(d["property_city"][0])
        if d.get("property_area"):
            zona = areas.get(d["property_area"][0])
    except Exception as e:
        print(f"Fincas Cala: sin ubicación REST para post {post_id}: {e}")
    if zona:
        # "Ciutadella (ciudad)" / "Ferreries (pueblo)" -> solo el municipio
        zona = re.sub(r"\s*\((ciudad|pueblo)\)\s*$", "", zona, flags=re.I).strip()
    partes = []
    for p in (ciudad, zona):
        if p and p.lower() not in [x.lower() for x in partes]:
            partes.append(p)
    return "; ".join(partes) if partes else None


def scrape_fincascala_detalle(url, referencia=None):
    """Scraper de una ficha de Fincas Cala (Houzez)."""
    try:
        r = SESSION.get(url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, "html.parser")

        def _num(txt):
            if not txt:
                return None
            m = re.search(r"\d[\d\.]*(?:,\d+)?", txt)
            if not m:
                return None
            try:
                return int(float(m.group(0).replace(".", "").replace(",", ".")))
            except ValueError:
                return None

        # ---------- Detalles (lista "Detalles" de Houzez) ----------
        detalles = {}
        for li in soup.select("#property-detail-wrap li, .property-detail-wrap li"):
            k = li.find("strong")
            v = li.find("span")
            if k and v:
                detalles[k.get_text(" ", strip=True).rstrip(":").strip().lower()] = v.get_text(" ", strip=True)

        def _det(*claves):
            for c in claves:
                for k, v in detalles.items():
                    if k.startswith(c):
                        return v
            return None

        # ---------- Título ----------
        titulo = None
        tw = soup.select_one(".property-title-price-wrap .page-title h1, .page-title-wrap h1, h1")
        if tw:
            titulo = tw.get_text(" ", strip=True)
            titulo = re.sub(r'[\s,–-]*Ref\.?[\s.:–-]*\d+\s*$', '', titulo, flags=re.IGNORECASE).strip()

        # ---------- Referencia ----------
        if not referencia:
            referencia = _det("referencia")
            if not referencia:
                m = re.search(r"ref-(\d+)", url)
                referencia = m.group(1) if m else url.rstrip("/").split("/")[-1]

        # ---------- Precio + estado (SOLO precio y etiquetas de la ficha) ----------
        precio_txt = None
        pe = soup.select_one(".property-title-price-wrap .item-price")
        if pe:
            precio_txt = pe.get_text(" ", strip=True)
        if not precio_txt:
            precio_txt = _det("precio")

        estado = _fincascala_estado_desde_texto(precio_txt)
        etiquetas = [a.get_text(" ", strip=True)
                     for a in soup.select(".property-labels-wrap a, .property-labels-wrap span")]
        if not estado:
            for et in etiquetas + [_det("estado de la propiedad", "etiqueta") or ""]:
                estado = _fincascala_estado_desde_texto(et)
                if estado:
                    break
        vendido = estado in ("VENDIDO", "RESERVADO")

        precio = None
        if precio_txt and not estado and re.search(r"\d", precio_txt):
            precio = _num(precio_txt)

        # ---------- Características ----------
        metros = _num(_det("tamaño de la propiedad", "superficie"))
        metros_parcela = _num(_det("tamaño parcela", "tamaño del terreno", "parcela"))
        habitaciones = _num(_det("dormitorio", "habitacion"))
        banos = _num(_det("cuartos de baño", "cuarto de baño", "baño"))
        tipo_txt = _det("tipo de propiedad")

        # ---------- Descripción / flags ----------
        desc_el = soup.select_one(".property-description-wrap")
        descripcion = desc_el.get_text(" ", strip=True) if desc_el else ""
        flags = detectar_flags(descripcion)

        # alquiler: solo si el estado Houzez de la ficha es exclusivamente alquiler
        est_houzez = {e.upper() for e in etiquetas if e}
        alquiler = bool(est_houzez) and est_houzez <= _FINCASCALA_ESTADOS_ALQUILER

        # ---------- Tipo ----------
        tipo = detectar_tipo(tipo_txt) or detectar_tipo(titulo) or (tipo_txt or None)

        # ---------- Ubicación (REST por postid; por defecto Ciutadella) ----------
        post_id = None
        body = soup.find("body")
        if body:
            m = re.search(r"postid-(\d+)", " ".join(body.get("class", [])))
            if m:
                post_id = m.group(1)
        if not post_id:
            sl = soup.find("link", rel="shortlink")
            m = re.search(r"[?&]p=(\d+)", sl.get("href", "")) if sl else None
            post_id = m.group(1) if m else None
        ubic_raw = _fincascala_ubicacion(post_id)
        # estandarizar_ubicacion puede devolver ya "Municipio; Zona" para una zona
        # (p.ej. 'cala blanca' -> 'Ciutadella; Cala Blanca'): se estandariza cada
        # parte por separado y se eliminan duplicados.
        partes_ubic = []
        for parte in (ubic_raw or "Ciutadella").split(";"):
            est = estandarizar_ubicacion(parte.strip()) if parte.strip() else None
            for sub in (est or "").split(";"):
                sub = sub.strip()
                if sub and sub.lower() not in [p.lower() for p in partes_ubic]:
                    partes_ubic.append(sub)
        ubicacion = "; ".join(partes_ubic) or "Ciutadella"

        # ---------- Galería (solo la galería superior de la ficha) ----------
        galeria = []
        for sel in (".top-gallery-section img", ".lightbox-gallery-wrap img"):
            for img in soup.select(sel):
                src = img.get("data-src") or img.get("src") or ""
                if not src or src.startswith("data:") or "/wp-content/uploads/" not in src:
                    continue
                if "logo" in src.lower():
                    continue
                src = urljoin(url, src)
                if src not in galeria:
                    galeria.append(src)
            if galeria:
                break
        og = soup.find("meta", property="og:image")
        imagen_destacada = (og.get("content") if og and og.get("content") else "") or (galeria[0] if galeria else "")

        return crear_propiedad_estandar(
            referencia=referencia,
            titulo=titulo,
            ubicacion=ubicacion,
            precio=precio,
            metros=metros,
            metros_parcela=metros_parcela,
            habitaciones=habitaciones,
            banos=banos,
            tipo=tipo,
            estado=estado,
            piscina=flags["piscina"],
            garaje=flags["garaje"],
            ascensor=flags["ascensor"],
            vistas_mar=flags["vistas_mar"],
            vendido=vendido,
            alquiler=alquiler,
            url_detalle=url,
            inmobiliaria="Fincas Cala",
            imagen_destacada=imagen_destacada,
            galeria=galeria,
        )
    except Exception as e:
        print(f"Error scrapeando Fincas Cala {url}: {e}")
        return None


# ===== FINQUES 2030 (Ciutadella; plataforma Inmoweb) =====
#
# Para pegar en scraper_historico.py (usa HEADERS, detectar_flags, detectar_tipo,
# estandarizar_ubicacion, crear_propiedad_estandar, _ubicacion_menorca y _pm_clean_int).
#
# Notas de la web:
#  - El castellano es el idioma por defecto en la raíz (/es/... redirige con 301 a /...).
#  - robots.txt (User-agent: *) prohíbe URLs con query que contengan modo=, od=, dt=, i= o c=.
#    La paginación del buscador usa &i=12&c=12 -> NO se puede seguir. Por eso se recorren la
#    página 1 del buscador de venta (?id_tipo_operacion=1, permitida) y las páginas de categoría
#    de venta (/casas-chalets-en-venta-3-1.html, /pisos-en-venta-24-1.html...), que van por ruta.
#    Si una categoría tuviera más de una página y su enlace siguiente también fuera de query
#    prohibida, se completa con las fichas "-esNNN.html" de /sitemap.xml (el detalle descarta
#    las que no sean "Tipo de operación: Venta").
#  - Sin Crawl-delay; se espera 1 s entre peticiones igualmente.
#  - Estado: <span class="etiqueta">Reservado</span> dentro de la tarjeta del listado
#    (div.venta[data-url]) y dentro de <div id="etiqueta"> en la ficha.

FINQUES2030_BASE = "https://www.finques2030.com"
FINQUES2030_LISTADO = FINQUES2030_BASE + "/results/?id_tipo_operacion=1"   # 1 = venta
FINQUES2030_DELAY = 1
_estados_finques2030 = {}          # url -> 'RESERVADO' | 'VENDIDO' | '' (leído del listado)
_finques2030_robots = []           # reglas Disallow (regex) del grupo User-agent: *
_finques2030_robots_cargado = [False]


def _finques2030_estado(txt):
    """('VENDIDO'|'RESERVADO'|'', vendido) a partir del texto/clase de una etiqueta concreta (es/ca/en)."""
    t = (txt or '').upper()
    if re.search(r'\b(VENDID[OA]S?|VENUD[AE]S?|VENUTS?|SOLD)\b', t):
        return 'VENDIDO', True
    if re.search(r'\b(RESERVAD[OA]S?|RESERVAT(?:S|DA|DES)?|RESERVED|UNDER OFFER)\b', t):
        return 'RESERVADO', True
    return '', False


def _finques2030_permitido(url):
    """robots.txt con comodines (* y $), que urllib.robotparser no entiende."""
    if not _finques2030_robots_cargado[0]:
        _finques2030_robots_cargado[0] = True
        try:
            r = SESSION.get(FINQUES2030_BASE + "/robots.txt", headers=HEADERS, timeout=20)
            grupo, en_grupo_star = [], False
            for linea in r.text.splitlines():
                linea = linea.split('#')[0].strip()
                if ':' not in linea:
                    continue
                k, v = [x.strip() for x in linea.split(':', 1)]
                if k.lower() == 'user-agent':
                    en_grupo_star = (v == '*')
                elif k.lower() == 'disallow' and en_grupo_star and v:
                    patron = re.escape(v).replace(r'\*', '.*')
                    if patron.endswith(r'\$'):
                        patron = patron[:-2] + '$'
                    grupo.append(re.compile(patron))
            _finques2030_robots.extend(grupo)
        except Exception as e:
            print(f"  Finques 2030: no se pudo leer robots.txt ({e})")
    p = urlparse(url)
    ruta = p.path + ('?' + p.query if p.query else '')
    return not any(rx.match(ruta) for rx in _finques2030_robots)


def _finques2030_get(url):
    if not _finques2030_permitido(url):
        print(f"  Finques 2030: robots.txt no permite {url}")
        return None
    r = SESSION.get(url, headers=HEADERS, timeout=30)
    r.raise_for_status()
    return r


def _finques2030_tarjetas(soup, urls, vistos):
    """Añade (referencia, url) de las tarjetas de un listado y guarda el estado de su etiqueta."""
    nuevas = 0
    for card in soup.select("div[data-url][id]"):
        principal = card.select_one(".sliderPrincipal[data-ref]")
        href = card.get("data-url", "")
        if not principal or not re.search(r'-es\d+\.html$', href):
            continue
        # La clase de la tarjeta es la operación ("venta"); se descarta cualquier otra
        if 'venta' not in (card.get('class') or []):
            continue
        url = urljoin(FINQUES2030_BASE, href)
        if url in vistos:
            continue
        vistos.add(url)
        ref_el = card.select_one(".numeroRef")
        referencia = (ref_el.get_text(strip=True) if ref_el else '') or principal.get("data-ref") \
            or f"F2030-{card.get('id')}"
        etiqueta = card.find("span", class_="etiqueta", recursive=False)
        _estados_finques2030[url] = _finques2030_estado(etiqueta.get_text(" ", strip=True))[0] if etiqueta else ''
        urls.append((referencia, url))
        nuevas += 1
    return nuevas


def obtener_urls_finques2030():
    """URLs de inmuebles en VENTA de Finques 2030 (ver notas arriba sobre paginación y robots)."""
    urls, vistos = [], set()
    total = None
    try:
        r = _finques2030_get(FINQUES2030_LISTADO)
    except Exception as e:
        print(f"Error obteniendo listado Finques 2030: {e}")
        return urls
    if r is None:
        return urls
    soup = BeautifulSoup(r.text, "lxml")
    m = re.search(r'Mostrando\s+\d+\s+a\s+\d+\s+de\s+(\d+)', soup.get_text(" ", strip=True))
    total = int(m.group(1)) if m else None
    _finques2030_tarjetas(soup, urls, vistos)

    # Categorías de venta (enlaces por ruta "...-en-venta-<tipo>-1.html", sin query)
    categorias = []
    for a in soup.select("a[href]"):
        href = a["href"].strip()
        if re.fullmatch(r'/[a-z0-9-]+-en-venta-\d+-1\.html', href) and href not in categorias:
            categorias.append(href)

    for cat in categorias:
        siguiente, paginas = urljoin(FINQUES2030_BASE, cat), 0
        while siguiente and paginas < 20:
            if total is not None and len(urls) >= total:
                break
            time.sleep(FINQUES2030_DELAY)
            try:
                r = _finques2030_get(siguiente)
            except Exception as e:
                print(f"Error en categoría Finques 2030 {siguiente}: {e}")
                break
            if r is None:
                break
            csoup = BeautifulSoup(r.text, "lxml")
            _finques2030_tarjetas(csoup, urls, vistos)
            paginas += 1
            nxt = csoup.select_one("ul.pagination a.next[href]")
            siguiente = urljoin(FINQUES2030_BASE, nxt["href"]) if nxt else None
            if siguiente and not _finques2030_permitido(siguiente):
                siguiente = None

    # Respaldo: fichas en castellano del sitemap si aún faltan (el detalle filtra por venta)
    if total is not None and len(urls) < total:
        time.sleep(FINQUES2030_DELAY)
        try:
            r = _finques2030_get(FINQUES2030_BASE + "/sitemap.xml")
            for loc in re.findall(r'<loc>([^<]+)</loc>', r.text if r else ''):
                m2 = re.search(r'^https://www\.finques2030\.com/[a-z0-9-]+-es(\d+)\.html$', loc.strip())
                if m2 and loc.strip() not in vistos:
                    vistos.add(loc.strip())
                    urls.append((f"F2030-{m2.group(1)}", loc.strip()))
        except Exception as e:
            print(f"Error leyendo sitemap Finques 2030: {e}")

    print(f"  Finques 2030: {len(urls)} URLs" + (f" (el listado dice {total})" if total is not None else ""))
    return urls


def scrape_finques2030_detalle(url, referencia=None):
    """Ficha de finques2030.com/<slug>-esNNNNNNN.html (Inmoweb)."""
    try:
        r = _finques2030_get(url)
        if r is None:
            return None
        soup = BeautifulSoup(r.text, "lxml")
        ficha = soup.select_one("#ficha")
        if not ficha:
            print(f"  Finques 2030: ficha sin #ficha {url}")
            return None

        # Datos de la lista "Detalle" (Tipo de propiedad, operación, Población, Zona, superficies...)
        datos = {}
        for li in ficha.select(".detallesFicha li, .caracteristicasPrincipales li"):
            st = li.find("strong")
            if not st:
                continue
            clave = st.get_text(" ", strip=True).rstrip(':').strip().lower()
            valor = li.get_text(" ", strip=True)[len(st.get_text(" ", strip=True)):].strip()
            datos.setdefault(clave, valor)

        operacion = datos.get('tipo de operación', '')
        if operacion and 'venta' not in operacion.lower():
            return None   # alquiler u otra operación

        ref_el = ficha.select_one(".headerLeft p span")
        if ref_el and ref_el.get_text(strip=True):
            referencia = ref_el.get_text(strip=True)

        h1 = ficha.select_one(".headerLeft h1")
        titulo = h1.get_text(" ", strip=True) if h1 else None
        if titulo:
            titulo = re.sub(r',\s*venta\s*$', '', titulo, flags=re.IGNORECASE)

        precio_el = ficha.select_one(".headerRight .precio")
        precio_txt = precio_el.get_text(" ", strip=True) if precio_el else ''
        m = re.search(r'\d[\d.]*', precio_txt)
        precio = _pm_clean_int(m.group(0)) if m else None

        def _num(clave):
            m = re.search(r'\d[\d.]*', datos.get(clave, ''))
            return int(m.group(0).replace('.', '')) if m else None

        metros = _num('sup. construida') or _num('sup. útil')
        metros_parcela = _num('sup. parcela')
        habitaciones = _num('habitaciones')
        banos = _num('baños')

        # Ubicación: Población (municipio) + Zona
        poblacion = datos.get('población', '')
        zona = datos.get('zona', '')
        ubicacion = _ubicacion_menorca(poblacion) if poblacion else None
        if ubicacion and zona:
            # estandarizar_ubicacion('Cala Blanca') ya da 'Ciutadella; Cala Blanca'
            zona_std = _ubicacion_menorca(zona)
            if zona_std and zona_std != ubicacion and ';' not in ubicacion:
                ubicacion = zona_std if zona_std.startswith(ubicacion + ';') else f"{ubicacion}; {zona_std}"

        # Estado: etiqueta sobre la galería de la ficha (<div id="etiqueta"><span class="etiqueta">)
        # y, como apoyo, la etiqueta de la tarjeta del listado y el texto del precio.
        estado, vendido = '', False
        etq = ficha.select_one("#etiqueta .etiqueta, #etiqueta")
        if etq:
            estado, vendido = _finques2030_estado(" ".join(etq.get("class", [])) + " " + etq.get_text(" ", strip=True))
        if not estado:
            estado, vendido = _finques2030_estado(precio_txt)
        if not estado and _estados_finques2030.get(url):
            estado, vendido = _estados_finques2030[url], True

        # Descripción (bloque #descripcionFicha) + "Características" reales de la ficha (solo lista
        # lo que tiene; se ignoran valores "No"). No se usa el formulario de búsqueda avanzada, que
        # siempre muestra Piscina/Garaje/Ascensor/Vistas al mar.
        desc_el = ficha.select_one("#descripcionFicha")
        descripcion = desc_el.get_text(" ", strip=True) if desc_el else ''
        caracts = []
        for bloque in ficha.select(".detallesFicha"):
            h3 = bloque.find("h3")
            if h3 and h3.get_text(strip=True).lower().startswith('caracter'):
                for li in bloque.select("li"):
                    st = li.find("strong")
                    if not st:
                        continue
                    k = st.get_text(" ", strip=True).rstrip(':')
                    v = li.get_text(" ", strip=True)[len(st.get_text(" ", strip=True)):].strip()
                    if v.lower().startswith('no') and not v.lower().startswith('no acristal'):
                        continue
                    if k.lower() == 'vistas':
                        caracts.append(f"vistas {v.lower()}")   # "Al mar" -> "vistas al mar"
                    else:
                        caracts.append(k)
        flags = detectar_flags(f"{descripcion} {' '.join(caracts)}")

        tipo_prop = datos.get('tipo de propiedad', '')
        if re.search(r'casa de campo|r[uú]stic', tipo_prop, re.IGNORECASE):
            tipo = 'Finca'
        else:
            tipo = detectar_tipo(tipo_prop) or detectar_tipo(titulo)

        # Galería: enlaces de la fotorama de la ficha (data-full = /image/w/N.jpg, ~1200 px)
        galeria = []
        for a in ficha.select("#sliderPropiedad a.imagen[data-full], #sliderPropiedad a.imagen[href]"):
            src = a.get("data-full") or a.get("href")
            if not src:
                continue
            if src.startswith("//"):
                src = "https:" + src
            if '/property/' in src and src not in galeria:
                galeria.append(src)
        if not galeria:
            img = ficha.select_one(".header > img[src]")
            if img:
                galeria.append(urljoin(url, img["src"]))
        imagen_destacada = galeria[0] if galeria else ''

        return crear_propiedad_estandar(
            referencia=referencia,
            titulo=titulo,
            ubicacion=ubicacion,
            precio=precio,
            metros=metros,
            metros_parcela=metros_parcela,
            habitaciones=habitaciones,
            banos=banos,
            tipo=tipo,
            estado=estado,
            piscina=flags['piscina'],
            garaje=flags['garaje'],
            ascensor=flags['ascensor'],
            vistas_mar=flags['vistas_mar'],
            vendido=vendido,
            alquiler=False,
            url_detalle=url,
            inmobiliaria='Finques 2030',
            imagen_destacada=imagen_destacada,
            galeria=galeria,
        )
    except Exception as e:
        print(f"Error scrapeando Finques 2030 {url}: {e}")
        return None


def procesar_listado(propiedades: List[Dict], nombre_inmobiliaria: str,
                     registro: RegistroScraping, gestor: GestorPropiedades) -> int:
    """Guarda las propiedades leídas de un listado completo y marca como eliminadas las que ya no aparecen"""
    if not propiedades:
        print(f"No se encontraron propiedades en {nombre_inmobiliaria}")
        return 0

    urls_actuales = {p['url_detalle'] for p in propiedades}
    urls_previas = {p['url_detalle'] for p in gestor.propiedades_actuales
                    if p.get('inmobiliaria') == nombre_inmobiliaria and p.get('estado') != 'ELIMINADO_WEB'}
    urls_eliminadas = urls_previas - urls_actuales
    if urls_eliminadas:
        registro.marcar_urls_eliminadas(urls_eliminadas)
        gestor.marcar_propiedades_eliminadas(urls_eliminadas)

    for prop in propiedades:
        gestor.agregar_propiedad(prop)
        registro.registrar_url_escaneada(prop['url_detalle'], prop.get('precio'), prop.get('estado'))

    nuevas = len(urls_actuales - urls_previas)
    print(f"  ✅ {nombre_inmobiliaria}: {len(propiedades)} en listado, {nuevas} nuevas, {len(urls_eliminadas)} eliminadas")
    return nuevas


def main():
    """Función principal con sistema eficiente mejorado"""
    modo = "PRODUCCIÓN" if PRODUCCION else f"TEST (máx. {LIMITE_TEST} propiedades por inmobiliaria)"
    tipo_escaneo = "COMPLETO" if E_COMPLETO else "INCREMENTAL"
    
    print(f"🏠🏠🏠 SCRAPER EFICIENTE DE INMOBILIARIAS 🏠🏠🏠")
    print(f"Modo: {modo}")
    print(f"Tipo de escaneo: {tipo_escaneo}")
    print("=" * 60)
    
    # Inicializar sistemas
    registro = RegistroScraping(ARCHIVO_REGISTRO)
    gestor = GestorPropiedades(ARCHIVO_PROPIEDADES, ARCHIVO_TEMP, ARCHIVO_HISTORICO)
    
    # Mostrar estadísticas iniciales
    total_conocidas = len(registro.obtener_urls_conocidas())
    total_existentes = len(gestor.propiedades_actuales)
    print(f"📊 URLs conocidas en registro: {total_conocidas}")
    print(f"📊 Propiedades existentes: {total_existentes}")
    
    if E_COMPLETO:
        print("🔄 Modo COMPLETO: Verificando cambios en todas las propiedades...")
    else:
        print("⚡ Modo INCREMENTAL: Buscando solo propiedades nuevas...")
    
    nuevas_total = 0
    actualizadas_total = 0
    
    # Ejecutar scrapers
    inmobiliarias = [
        (scrape_fincasllongas_detalle, "Fincas Llongas", obtener_urls_fincasllongas),
        (scrape_artrutx_detalle, "Inmobiliaria Artrutx", obtener_urls_artrutx),
        (scrape_fincasciutadella_detalle, "Fincas Ciutadella", obtener_urls_fincasciutadella),
        (scrape_inmomenorcacentro_detalle, "Inmo Menorca Centro", obtener_urls_inmomenorcacentro),
        (scrape_inmobiliariapalau_detalle, "Inmobiliaria Palau", obtener_urls_inmobiliariapalau),
        (scrape_bonninsanso_detalle, "Bonnin Sanso", obtener_urls_bonninsanso),
        (scrape_fincasarmengol_detalle, "Fincas Armengol", obtener_urls_fincasarmengol),
        (scrape_fincasfaro_detalle, "Fincas Faro", obtener_urls_fincasfaro),
        (scrape_zenhousecredit_detalle, "Zenhouse Credit", obtener_urls_zenhousecredit),
        (scrape_enprimeralinea_detalle, "En Primera Línea", obtener_urls_enprimeralinea),
        (scrape_casasenmenorca_detalle, "Casas en Menorca", obtener_urls_casasenmenorca),
        (scrape_fincasseminari_detalle, "Fincas Seminari", obtener_urls_fincasseminari),
        (scrape_inmocampsbosch_detalle, "Inmobiliaria Camps Bosch", obtener_urls_inmocampsbosch),
        (scrape_portalmenorca_detalle, "Portal Menorca", obtener_urls_portalmenorca),
        (scrape_vidalmenorca_detalle, "Vidal Menorca", obtener_urls_vidalmenorca),
        (scrape_menorcasa_detalle, "Menorcasa", obtener_urls_menorcasa),
        (scrape_saimmobiliaria_detalle, "SA Inmobiliaria", obtener_urls_saimmobiliaria),
        (scrape_3villas_detalle, "3Villas",obtener_urls_3villas),
        (scrape_fincascala_detalle, "Fincas Cala", obtener_urls_fincascala),
        (scrape_fincasmenorquinas_detalle, "Fincas Menorquinas", obtener_urls_fincasmenorquinas),
        (scrape_lucasfox_detalle, "Lucas Fox", obtener_urls_lucasfox),
        (scrape_finques2030_detalle, "Finques 2030", obtener_urls_finques2030),
    ]

    """ Prortal menorca incluye
    -HOME MENORCA
    -FINCAS MANTOLAN
    -MENORCA IN PERSON
    -FINCAS SANT LLUIS
    -FINCAS SUNSHINE
    -FINCAS VENALIS
    """

    for scraper_func, nombre, obtener_urls_func in inmobiliarias:
        try:
            propiedades_nuevas = scraper_eficiente_website(
                scraper_func=scraper_func,
                nombre_inmobiliaria=nombre,
                registro=registro,
                gestor=gestor,
                obtener_urls_func=obtener_urls_func
            )
            nuevas_total += len(propiedades_nuevas)
        except Exception as e:
            print(f"❌ Error con {nombre}: {e}")


    # Inmobiliarias que se leen enteras desde el listado (cada noche se actualizan todas)
    listados = [
        ("Pons Morales", lambda: scrape_mobilia_listado("https://www.ponsmorales.com/es/venta", "Pons Morales")),
        ("Finques Torres", lambda: scrape_mobilia_listado("https://www.finquestorres.net/es/venta", "Finques Torres")),
        ("Blanca de Olivar", lambda: scrape_mobilia_listado("https://www.blancadeolivar.com/es/venta", "Blanca de Olivar")),
        ("Finques Fuguet", scrape_finquesfuguet_listado),
    ]
    for nombre, scraper_listado in listados:
        try:
            nuevas_total += procesar_listado(scraper_listado(), nombre, registro, gestor)
        except Exception as e:
            print(f"❌ Error con {nombre}: {e}")

    # Finalizar y guardar (con opción de organizar por inmobiliaria)
    GUARDAR_POR_INMOBILIARIA = False  # Configurar según preferencia
    total_final = gestor.finalizar_y_guardar(guardar_por_inmobiliaria=GUARDAR_POR_INMOBILIARIA)
    
    if E_COMPLETO:
        registro.marcar_ejecucion_completa()
    
    registro.guardar_registro()
    
    print("\n" + "=" * 60)
    print("✅ SCRAPING COMPLETADO")
    print(f"📊 Propiedades disponibles en el feed: {total_final}")
    print(f"🗂️ Histórico completo: {ARCHIVO_HISTORICO}")
    print(f"💾 Archivo guardado: {ARCHIVO_PROPIEDADES}")
    print(f"📝 Registro actualizado: {ARCHIVO_REGISTRO}")
    
    if GUARDAR_POR_INMOBILIARIA:
        print("🗂️ Propiedades organizadas por inmobiliaria")
    
    if E_COMPLETO:
        print(f"🔄 Propiedades verificadas/actualizadas: {actualizadas_total}")
    else:
        print(f"⚡ Propiedades nuevas encontradas: {nuevas_total}")

if __name__ == "__main__":
    main()
