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
LIMITE_TEST = 900    # Límite de propiedades en modo test
E_COMPLETO = False  # False = incremental (novedades), True = completo (verificar cambios)

# Archivos de datos
#ARCHIVO_PROPIEDADES = 'propiedades_menorca_estandarizado.json'
#ARCHIVO_REGISTRO = 'registro_scraping.json'
#ARCHIVO_TEMP = 'propiedades_temp.json'
# Directorio de datos (por defecto ".", pero lo podremos fijar a "public")
DATA_DIR = os.getenv('DATA_DIR', '.')

# Asegurar que existe el directorio
os.makedirs(DATA_DIR, exist_ok=True)

# Archivos de datos (parametrizables por ENV, con defaults en DATA_DIR)
ARCHIVO_PROPIEDADES = os.getenv('ARCHIVO_PROPIEDADES',
                                os.path.join(DATA_DIR, 'propiedades_menorca_estandarizado.json'))
ARCHIVO_REGISTRO   = os.getenv('ARCHIVO_REGISTRO',
                                os.path.join(DATA_DIR, 'registro_scraping.json'))
ARCHIVO_TEMP       = os.getenv('ARCHIVO_TEMP',
                                os.path.join(DATA_DIR, 'propiedades_temp.json'))


# Diccionario global para almacenar estados desde el listado
_estados_fincasseminari = {}
_estados_inmocampsbosch = {}


HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/115 Safari/537.36"
}

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
    'SOLAR': 'Solar',
    'PARCELA': 'Solar',
    'GARAJE': 'Garaje',
    'PARKING': 'Garaje',
    'TERRENO': 'Terreno',
    'HUERTO': 'Huerto',
    'FINCA': 'Finca',
    'CASA CAMPO': 'Finca',
    'NAVE': 'Nave',
    'OFICINA': 'Oficina',
    'EDIFICIO SINGULAR': 'Edificio',
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
        'Maó/Mahón': 'Maó',
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
        'cala\'n bosch': 'Ciutadella; Cap d\'Artrutx'
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
    
    def __init__(self, archivo_propiedades: str, archivo_temp: str):
        self.archivo_propiedades = archivo_propiedades
        self.archivo_temp = archivo_temp
        self.propiedades_actuales = self._cargar_propiedades()
        self.propiedades_procesadas = []
        self.propiedades_por_inmobiliaria = {}  # Nuevo: organizar por inmobiliaria
    
    def _cargar_propiedades(self) -> List[Dict]:
        """Carga propiedades existentes"""
        if os.path.exists(self.archivo_propiedades):
            try:
                with open(self.archivo_propiedades, 'r', encoding='utf-8') as f:
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
        """Calcula hash basado en precio y estado"""
        precio = propiedad.get('precio')
        estado = propiedad.get('estado')
        precio_str = str(precio) if precio is not None else "None"
        estado_str = str(estado) if estado is not None else "None"
        contenido = f"{precio_str}|{estado_str}"
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
        if E_COMPLETO:
            todas_propiedades = self.propiedades_actuales + self.propiedades_procesadas
        else:
            todas_propiedades = self.propiedades_actuales + self.propiedades_procesadas
        
        # Eliminar duplicados por URL (mantener la más reciente por fecha_scraping)
        propiedades_unicas = {}
        for prop in todas_propiedades:
            url = prop['url_detalle']
            if url not in propiedades_unicas:
                propiedades_unicas[url] = prop
            else:
                # Comparar fechas de scraping para mantener la más antigua (primera vez encontrada)
                fecha_actual = prop.get('fecha_scraping', '')
                fecha_existente = propiedades_unicas[url].get('fecha_scraping', '')
                
                if fecha_actual < fecha_existente:
                    # Preservar fecha original pero actualizar el resto
                    prop_actualizada = prop.copy()
                    prop_actualizada['fecha_scraping'] = fecha_actual
                    propiedades_unicas[url] = prop_actualizada
                elif fecha_actual > fecha_existente:
                    # Mantener la existente que tiene fecha más antigua
                    pass
                else:
                    # Misma fecha, usar la más reciente por fecha_ultima_actualizacion
                    if prop.get('fecha_ultima_actualizacion', '') > propiedades_unicas[url].get('fecha_ultima_actualizacion', ''):
                        propiedades_unicas[url] = prop
        
        resultado_final = list(propiedades_unicas.values())
        
        try:
            if guardar_por_inmobiliaria:
                # Organizar por inmobiliaria
                propiedades_organizadas = {}
                for prop in resultado_final:
                    inmobiliaria = prop.get('inmobiliaria', 'Desconocida')
                    if inmobiliaria not in propiedades_organizadas:
                        propiedades_organizadas[inmobiliaria] = []
                    propiedades_organizadas[inmobiliaria].append(prop)
                
                # Guardar en formato organizado
                with open(self.archivo_propiedades, 'w', encoding='utf-8') as f:
                    json.dump(propiedades_organizadas, f, ensure_ascii=False, indent=2)
            else:
                # Guardar en formato plano (lista)
                with open(self.archivo_propiedades, 'w', encoding='utf-8') as f:
                    json.dump(resultado_final, f, ensure_ascii=False, indent=2)
            
            # Limpiar archivo temporal
            if os.path.exists(self.archivo_temp):
                os.remove(self.archivo_temp)
                
            return len(resultado_final)
        except Exception as e:
            print(f"Error guardando archivo final: {e}")
            return 0


def crear_propiedad_estandar(**kwargs):
    """Crea una propiedad con estructura estandarizada mejorada"""

    precio = kwargs.get('precio', None)
    alquiler = kwargs.get('alquiler', False)

    # 🔽 Nueva validación: si es alquiler y el precio supera 6000€, marcar como False
    if alquiler and precio and precio > 6000:
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
        "vendido": kwargs.get('vendido', False),
        "alquiler": kwargs.get('alquiler', False),
        "url_detalle": kwargs.get('url_detalle', ''),
        "inmobiliaria": kwargs.get('inmobiliaria', ''),
        "imagen_destacada": kwargs.get('imagen_destacada', ''),
        "galeria": kwargs.get('galeria', []),
        "fecha_scraping": kwargs.get('fecha_scraping', datetime.now().isoformat()),  # Permitir override
        "fecha_ultima_actualizacion": kwargs.get('fecha_ultima_actualizacion', None)  # Nueva para tracking
    }

def is_allowed(url):
    """Verifica si el scraping está permitido por robots.txt"""
    parsed = urlparse(url)
    base = f"{parsed.scheme}://{parsed.netloc}"
    robots_url = urljoin(base, "/robots.txt")
    rp = urllib.robotparser.RobotFileParser()
    try:
        rp.set_url(robots_url)
        rp.read()
        return rp.can_fetch(HEADERS['User-Agent'], url)
    except:
        print(f"No se pudo acceder a {robots_url}")
        return True

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
    
    # Filtrar URLs según el modo
    for referencia, url in urls_disponibles:
        if not E_COMPLETO and url in urls_conocidas:
            # En modo incremental, solo procesar si no conocemos la URL
            if url not in propiedades_existentes:
                urls_a_procesar.append((referencia, url))
                urls_nuevas += 1
            else:
                urls_omitidas += 1
        else:
            # En modo completo o URL nueva
            urls_a_procesar.append((referencia, url))
            if url not in urls_conocidas:
                urls_nuevas += 1

    urls_conocidas_inmo = {
        u for u in urls_conocidas
        if any(prop.get('inmobiliaria') == nombre_inmobiliaria
               for prop in gestor.propiedades_actuales
               if prop['url_detalle'] == u)
    }
    
    print(f"  📊 URLs encontradas: {len(urls_disponibles)}")
    print(f"  📊 URLs conocidas ({nombre_inmobiliaria}): {len(urls_conocidas_inmo)}")
    print(f"  📊 URLs nuevas: {urls_nuevas}")
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
                if E_COMPLETO and url in propiedades_existentes:
                    # Modo completo: verificar cambios preservando fecha original
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
        resp = requests.get(sitemap_url, headers=HEADERS)
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
        resp = requests.get(subsitemap_url, headers=HEADERS)
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
        r = requests.get(url, headers=HEADERS, timeout=30)
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
        r = requests.get(url_listado, headers=HEADERS, timeout=30)
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
        r = requests.get(url, headers=HEADERS, timeout=30)
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
        r = requests.get(url_listado, headers=HEADERS, timeout=30)
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
        r = requests.get(url, headers=HEADERS, timeout=30)
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

    r = requests.get(url_listado, headers=HEADERS, timeout=30)
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
        r = requests.get(url_listado, headers=HEADERS, timeout=30)
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
        r = requests.get(url, headers=HEADERS, timeout=30)
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
        r = requests.get(sitemap_url, headers=HEADERS, timeout=30)
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
        r = requests.get(url, headers=HEADERS, timeout=30)
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
        r = requests.get(sitemap_url, headers=HEADERS, timeout=30)
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
        r = requests.get(url, headers=HEADERS, timeout=30)
        r.raise_for_status()
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
        for img in soup.select('img'):
            if img.has_attr('src'):
                src = img['src']
                if not any(x in src.lower() for x in ['logo','icon','/ee/','/caracts/','/static/']):
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
        r = requests.get(sitemap_url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        root = ET.fromstring(r.content)

        urls_propiedades = []
        url_tags = root.findall(".//{http://www.sitemaps.org/schemas/sitemap/0.9}url")
        for url_tag in url_tags:
            loc = url_tag.find("{http://www.sitemaps.org/schemas/sitemap/0.9}loc")
            if loc is not None and "/propiedad/" in loc.text:
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
        r = requests.get(url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, 'html.parser')
        for tag in soup(["header","footer"]):
            tag.decompose()

        # ===========================
        # TÍTULO + UBICACIÓN
        # ===========================
        titulo, ubicacion = None, None
        titulo_elem = soup.select_one("h2")
        if titulo_elem:
            raw = titulo_elem.get_text(strip=True)
            raw = re.sub(r'^[A-Z]-\d+(\s*\(\d+\))?\s*', '', raw)  # quitar ref inicial
            raw = re.sub(r'[–—-]', '-', raw).strip()
            m = re.search(r'\ben\s+([A-ZÁÉÍÓÚÜÑ][\w\s´’`]+)$', raw, re.IGNORECASE)
            if m:
                ubicacion = m.group(1).strip()
                titulo = raw
            else:
                partes = [p.strip() for p in raw.split('-') if p.strip()]
                if len(partes) > 1:
                    ubicacion, titulo = partes[-1], " - ".join(partes[:-1])
                else:
                    titulo = raw
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
        texto = soup.get_text()
        m = re.search(r'(\d+)\s*(?:habitacion|dormitorio)', texto, re.IGNORECASE)
        if m: habitaciones = int(m.group(1))
        m = re.search(r'(\d+)\s*baño', texto, re.IGNORECASE)
        if m: banos = int(m.group(1))
        m = re.search(r'(\d+)\s*m[2²]?\s*construid', texto, re.IGNORECASE)
        if m: metros = int(m.group(1))

        # ===========================
        # ESTADO
        # ===========================
        estado = None
        vendido = 'VENDIDO' in texto.upper()
        if vendido:
            estado = "VENDIDO"

        # ===========================
        # FLAGS
        # ===========================
        flags = detectar_flags(texto.upper())
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
                if not any(x in src.lower() for x in ['logo','icon','banner','/flags/']):
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
        r = requests.get(sitemap_url, headers=HEADERS, timeout=30)
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
        r = requests.get(url, headers=HEADERS, timeout=30)
        r.raise_for_status()
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
        r = requests.get(url_listado, headers=HEADERS, timeout=30)
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
        r = requests.get(url, headers=HEADERS, timeout=30)
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
        r = requests.get(sitemap_url, headers=HEADERS, timeout=30)
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
        r = requests.get(url, headers=HEADERS, timeout=30)
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
        r = requests.get(sitemap_url, headers=HEADERS, timeout=30)
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
        r = requests.get(url, headers=HEADERS, timeout=30)
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
            r = requests.get(url_listado, headers=HEADERS, timeout=30)
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
        r = requests.get(url, headers=HEADERS, timeout=30)
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
        r = requests.get(base_url, headers=HEADERS, timeout=30)
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
        r = requests.get(url, headers=HEADERS, timeout=30)
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
            r = requests.get(url_listado, headers=HEADERS, timeout=30)
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
        r = requests.get(url, headers=HEADERS, timeout=30)
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
        r = requests.get(sitemap_url, headers=HEADERS, timeout=30)
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
        r = requests.get(url, headers=HEADERS, timeout=30)
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

def obtener_urls_menorcasa():
    """Obtener todas las URLs de propiedades de Menorcasa desde el sitemap"""
    sitemap_url = "https://menorcasa.com/property-sitemap.xml"
    try:
        r = requests.get(sitemap_url, headers=HEADERS, timeout=30)
        r.raise_for_status()
        root = ET.fromstring(r.content)

        urls_propiedades = []
        url_elements = root.findall(".//{http://www.sitemaps.org/schemas/sitemap/0.9}url")
        for url_element in url_elements:
            loc_element = url_element.find("{http://www.sitemaps.org/schemas/sitemap/0.9}loc")
            if loc_element is not None:
                url = loc_element.text
                if "/es/property/" in url:
                    urls_propiedades.append((None, url))  # referencia se extrae en el detalle

        return list(set(urls_propiedades))
    except Exception as e:
        print(f"Error obteniendo URLs de Menorcasa: {e}")
        return []


def scrape_menorcasa_detalle(url, referencia=None):
    """Scraper específico para un detalle de propiedad en Menorcasa"""
    try:
        r = requests.get(url, headers=HEADERS, timeout=30)
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

        labels = [lbl.get_text(strip=True).upper() for lbl in soup.select(".rh_label__wrap")]

        if any("VENDIDA" in l or "RESERVADO" in l for l in labels):
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

         # Flags
        texto_completo = soup.get_text()
        flags = detectar_flags(texto_completo.upper())
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
        r = requests.get(sitemap_url, headers=HEADERS, timeout=30)
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
        r = requests.get(url, headers=HEADERS, timeout=30)
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
        r = requests.get(sitemap_url, headers=HEADERS, timeout=30)
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
        r = requests.get(url, headers=HEADERS, timeout=30)
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
    gestor = GestorPropiedades(ARCHIVO_PROPIEDADES, ARCHIVO_TEMP)
    
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


    # Pons Morales
    propiedades_ponsmorales = scrape_mobilia_listado("https://www.ponsmorales.com/es/venta", "Pons Morales")
    for prop in propiedades_ponsmorales:
        gestor.agregar_propiedad(prop)
        registro.registrar_url_escaneada(prop['url_detalle'], prop.get('precio'), prop.get('estado'))
 

    # Finques Torres
    propiedades_finquestorres = scrape_mobilia_listado("https://www.finquestorres.net/es/venta", "Finques Torres")
    for prop in propiedades_finquestorres:
        gestor.agregar_propiedad(prop)
        registro.registrar_url_escaneada(prop['url_detalle'], prop.get('precio'), prop.get('estado'))
    
    # Finalizar y guardar (con opción de organizar por inmobiliaria)
    GUARDAR_POR_INMOBILIARIA = False  # Configurar según preferencia
    total_final = gestor.finalizar_y_guardar(guardar_por_inmobiliaria=GUARDAR_POR_INMOBILIARIA)
    
    if E_COMPLETO:
        registro.marcar_ejecucion_completa()
    
    registro.guardar_registro()
    
    print("\n" + "=" * 60)
    print("✅ SCRAPING COMPLETADO")
    print(f"📊 Total de propiedades en archivo final: {total_final}")
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
