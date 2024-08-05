#!/usr/bin/env bash

# This script can be used to build a release version of the application and upload it as an asset of a Github release.
#
# Usage:
#   build-and-upload.sh <version>
#
# Requirements:
# - The GITHUB_TOKEN environment variable needs to be set.
# - The RELEASE_ID environment variable needs to be set.

set -e

if [ $# -ne 1 ]; then
    cat << EOF
Invalid number of arguments.

Usage:
  build-and-upload.sh <version>

Example:
  build-and-upload.sh 0.1.0
EOF
  exit 1
fi

version=$1
target=$(rustc -vV | grep host | cut -d ' ' -f2)

if [[ -z "${GITHUB_TOKEN}" ]]; then
  echo "Environment variable 'GITHUB_TOKEN' is missing."
  exit 1
fi
if [[ -z "${RELEASE_ID}" ]]; then
  echo "Environment variable 'RELEASE_ID' is missing."
  exit 1
fi

echo "Building release"
cargo build --release

echo "Compress release"

binaryDir="lator-${version}.${target}"
mkdir $binaryDir

mv ./target/release/lator "$binaryDir/"
if [[ "$target" = "windows" ]]
then
  # Add a .exe extension on the Windows release.
  mv "$binaryDir/lator" "$binaryDir/lator.exe"
fi

7z a lator.zip "$binaryDir"

echo "Uploading asset to Github release"

assetName="lator-${version}.${target}.zip"

curl -L --fail-with-body \
  -X POST \
  -H "Accept: application/vnd.github+json" \
  -H "Authorization: Bearer ${GITHUB_TOKEN}" \
  -H "X-GitHub-Api-Version: 2022-11-28" \
  -H "Content-Type: application/octet-stream" \
  "https://uploads.github.com/repos/theogilbert/lator/releases/${RELEASE_ID}/assets?name=${assetName}" \
  --data-binary "@lator.zip"

echo "Done"