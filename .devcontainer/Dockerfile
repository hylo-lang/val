# **Do not change without a global search/replace for this version string.**
ARG SWIFT_VERSION=5.10
# Other ARG declarations must follow FROM
FROM swift:${SWIFT_VERSION}

ARG HYLO_LLVM_BUILD_TYPE=MinSizeRel
ARG HYLO_LLVM_BUILD_RELEASE=20240303-215025
ARG HYLO_LLVM_VERSION=17.0.6

ENV HYLO_LLVM_DOWNLOAD_URL="https://github.com/hylo-lang/llvm-build/releases/download"

RUN apt install -y gnupg
RUN apt update
# llvm-15 is installed to get llvm-cov, which is needed to generate our coverage reports.
RUN apt install -y curl libzstd-dev libzstd1 lsb-release make ninja-build tar wget zstd software-properties-common python3-pip llvm-15

# Get a recent cmake (https://www.kitware.com//cmake-python-wheels/)
RUN if $(/usr/bin/which cmake) ; then apt purge --auto-remove cmake ; fi
RUN pip3 install --upgrade cmake

# Reclaim some disk, maybe.
RUN apt-get clean

# Get the LLVM build(s) for the host architecture
RUN <<EOT bash -ex -o pipefail

    file_prefix="llvm-\${HYLO_LLVM_VERSION}-\$(uname -m)-unknown-linux-gnu"
    url_prefix="\${HYLO_LLVM_DOWNLOAD_URL}/\${HYLO_LLVM_BUILD_RELEASE}/\$file_prefix"

    # Add 'Debug' to the loop below to install a debug build of LLVM
    # as well.  It is not there by default because it was causing us
    # to run out of disk space in GitHub CI.
    for build_type in MinSizeRel; do
        curl --no-progress-meter -L "\${url_prefix}-\${build_type}.tar.zst" | tar -x --zstd -C /opt
        ln -s /opt/\${file_prefix}-\${build_type} /opt/llvm-\${build_type}
    done

EOT

# Make and install the llvm.pc file.
ADD make-pkgconfig.sh /tmp
RUN <<EOT bash -ex -o pipefail

    export PATH="/opt/llvm-${HYLO_LLVM_BUILD_TYPE}/bin:\$PATH"
    /tmp/make-pkgconfig.sh /usr/local/lib/pkgconfig/llvm.pc > /dev/null
    rm /tmp/make-pkgconfig.sh

EOT
