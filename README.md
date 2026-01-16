
---

SATX es un paquete de software en Python diseñado para modelar, optimizar y tomar decisiones formales en problemas de tipo Wicked (problemas complejos, ambiguos y con múltiples actores) mediante la compilación a lógica de primer orden y resolución con solvers externos. Es una biblioteca que actúa como un compilador de restricciones a forma de Clausula Normal Conjuntiva (CNF), permitiendo la resolución de problemas de satisfacibilidad (SAT), conteo de soluciones (#SAT), optimización de soluciones (Weighted MaxSAT) y modelado de problemas de programación lineal entera (MIP) mediante la exportación de modelos a formatos estándar.

SATX no incluye solvers, sino que exporta el problema en formato DIMACS (para SAT/#SAT), WCNF (para Weighted MaxSAT) o LP/MPS (para MIP), y el usuario debe proporcionar solvers externos compatibles.

¿Qué es SATX?
SATX es una biblioteca de modelado y resolución formal que permite:

Modelar problemas mediante variables de tipo Unit (enteros bit-vector) y Fixed (punto fijo).
Definir restricciones (SAT, #SAT, MaxSAT, MIP) usando un DSL (Domain-Specific Language) declarativo y expresivo.
Compilar las restricciones a una representación interna (CNF) y a formatos externos (DIMACS, WCNF, LP, MPS).
Resolver problemas utilizando solvers externos (SAT, #SAT, MaxSAT, MIP).
Analizar resultados: obtener valores asignados, contar soluciones, calcular distribuciones de probabilidad condicional (a través de exposición y conteo), y relajar restricciones para encontrar soluciones factibles.
SATX está diseñado para problemas de "Wicked" (problemas complejos, ambiguos, con múltiples actores y restricciones), donde la formalización y la verificación son cruciales.

¿Qué puede hacer SATX?
SATX permite:

Modelar problemas en un lenguaje declarativo.
Definir restricciones (SAT, #SAT, MaxSAT, MIP) y resolverlas.
Exportar modelos a formatos estándar para solvers externos.
Analizar resultados (valores, conteo, distribuciones).
Combinar solvers (SAT, #SAT, MaxSAT, MIP) en un mismo flujo de trabajo.
Verificar propiedades de sistemas (por ejemplo, robustez, estabilidad, seguridad).

[SATX: Modelado y Decisión Formal en Sistemas Wicked - SAT, #SAT, Weighted MaxSAT y MIP](https://www.academia.edu/145768932/SATX_Modelado_y_Decisi%C3%B3n_Formal_en_Sistemas_Wicked_SAT_SAT_Weighted_MaxSAT_y_MIP)

---
## Estado actual

* **Versión de código público:** `SATX 0.4.0`
* **Versión de especificación:** `SATX 0.4.7` (Privada)

Consulte [`VERSIONING.md`](docs/VERSIONING.md) para obtener más información.

---

## Licencias

SATX tiene doble licencia:

* **AGPL v3** para uso de código abierto
* **Licencia comercial** para aplicaciones propietarias o de código cerrado.

Consulte `LICENSE.md` y `COMMERCIAL.md` para obtener más información.

---

## Autoría

SATX es creado y mantenido por **Oscar Riveros**.

---




