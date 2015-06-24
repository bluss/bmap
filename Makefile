CRATES = bmap

docs: mkdocs subst

$(CRATES): VERSION
	# Put in the crate version into the docs
	find ./doc/$@ -name "*.html" -exec sed -i -e "s/<title>\(.*\) - Rust/<title>$@ $(shell cat VERSION) - \1 - Rust/g" {} \;

subst: $(CRATES)

mkdocs:
	cargo doc
	rm -rf ./doc
	cp -r ./target/doc ./doc
	-cat ./custom.css >> doc/main.css

VERSION: Cargo.toml
	cargo pkgid | sed -e "s/.*#//" > VERSION

.PHONY: docs mkdocs subst $(CRATES)
