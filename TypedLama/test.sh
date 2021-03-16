#!/usr/bin/env bash

pushd regression
make regression
exitCode=$?
popd
exit $exitCode