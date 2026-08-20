FROM ubuntu:24.04

RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    curl \
    git \
    python3 \
    build-essential \
    && rm -rf /var/lib/apt/lists/*

ENV ELAN_HOME=/usr/local/elan
ENV PATH=/usr/local/elan/bin:$PATH

RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf \
      | sh -s -- -y --default-toolchain none --no-modify-path \
    && chmod -R a+w "$ELAN_HOME"
