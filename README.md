# Facilitio

Solving some facility layout problems with Z3 in Rust on WebAssembly

DEMO: https://ogukei.github.io/facilitio/

## Setup

Install the latest npm using n on Ubuntu 20.04 LTS. Skip this step if you have already installed npm.

```
sudo apt install nodejs npm
sudo npm install -g n
sudo n stable
sudo apt purge nodejs npm
exec $SHELL -l
node -v
npm -v
```

Execute npm install.
```
cd <repository-dir>/facilitio-web
npm install
```

## Build

```
npm run build
```

## Run

```
npm run serve
```
