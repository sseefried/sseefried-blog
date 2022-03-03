# Sean Seefried's Blog

This site is built using [Pandoc](https://pandoc.org/)

## Set up

Install Pandoc
```
$ cabal install pandoc
$ cabal install --lib pandoc-types
```

Install Agda
```
$ brew install agda
```

## Generate HTML, Build, Deploy

1. Generate the HTML for Agda posts

```
./regen.sh
```

2. Build

```
./build.sh
```

3. Deploy

```
./deploy.sh
```
