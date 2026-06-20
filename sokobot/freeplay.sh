#!/bin/bash
find . -name "*.class" -type f -delete
javac src/main/Driver.java -cp src
java -classpath src main.Driver "$1" fp
