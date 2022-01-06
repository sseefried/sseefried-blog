#!/bin/bash

TGT="tilthydeath:/var/www/seanseefried.org/blog"
echo "Deploying to $TGT"
rsync -avz site/* "$TGT"
