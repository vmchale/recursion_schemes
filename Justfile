update-docs:
    sn c .
    rm -rf docs
    idris --mkdoc recursion_schemes.ipkg
    mv recursion_schemes_doc/ docs/
