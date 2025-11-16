# FlowLang

Este proyecto contiene una implementación del lenguaje **FlowLang** en Racket
empleando la herramienta **SLLGEN**. El archivo principal es
[`flowlang.rkt`](flowlang.rkt); exporta la función `run`, que recibe una cadena
con el programa fuente y devuelve el valor resultante de la última expresión.

#lang racket

(require "flowlang.rkt")

(run "
var x = 5;
var y = 7;
print(x + y);
")

Nota: el entorno de ejecución debe contar con Racket y la librería eopl para poder ejecutar el intérprete.
