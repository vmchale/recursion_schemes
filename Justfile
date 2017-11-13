clean:
    sn c .
    rm -f tags

build:
    idris --build recursion_schemes.ipkg

test:
    idris --testpkg test.ipkg

update-docs:
    sn c .
    idris --build recursion_schemes.ipkg
    rm -rf docs
    idris --mkdoc recursion_schemes.ipkg
    mv recursion_schemes_doc/ docs/
