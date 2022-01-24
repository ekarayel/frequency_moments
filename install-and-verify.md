# Installation and Verification in Linux

Instructions for verification if Isabelle is *not* pre-installed. 

Prerequisites: `wget`, `git` and `x11-utils`.

In a fresh directory:

```bash
# Download and unpack Isabelle-2021-1
mkdir isabelle
wget -qO- https://isabelle.in.tum.de/website-Isabelle2021-1/dist/Isabelle2021-1_linux.tar.gz \
  | tar xz --strip-components=1 -C isabelle

# Download and unpack the AFP
mkdir afp
wget -qO- https://www.isa-afp.org/release/afp-2022-01-06.tar.gz | tar xz --strip-components=1 -C afp

# Install AFP
isabelle/bin/isabelle components -u afp/thys

# Clone this repo
git clone https://github.com/ekarayel/frequency_moments.git

# Plain Verification (requires 30 min)
isabelle/bin/isabelle build -D frequency_moments/thys/
```

If pdflatex is installed, it is possible to generate printable output, by adding following options to the isabelle build command:

```bash
-o document=pdf -o document_variants="document:outline=/proof" -o document_output=output
```
