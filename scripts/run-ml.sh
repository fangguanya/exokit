#!/bin/bash

set -e

source ./version-ml.sh

cmd.exe /c "$MLSDK_WIN/tools/mldb/mldb.exe" terminate -f com.webmr.exokit
cmd.exe /c "$MLSDK_WIN/tools/mldb/mldb.exe" launch com.webmr.exokit -v "ARGS=node . $@"
cmd.exe /c "$MLSDK_WIN/tools/mldb/mldb.exe" log exokit:*
