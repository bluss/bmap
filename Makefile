DOCCRATES = bmap

VERSIONS = $(patsubst %,target/VERS/%,$(DOCCRATES))

docs: mkdocs subst

# https://www.gnu.org/software/make/manual/html_node/Automatic-Variables.html
$(VERSIONS): Cargo.toml
	mkdir -p $(@D)
	cargo pkgid $(@F) | sed -e "s/.*#\(\|.*:\)//" > "$@"

$(DOCCRATES): %: target/VERS/%
	# Put in the crate version into the docs
	find ./doc/$@ -name "*.html" -exec sed -i -e "s/<title>\(.*\) - Rust/<title>$@ $(shell cat $<) - \1 - Rust/g" {} \;

subst: $(DOCCRATES)

mkdocs: Cargo.toml
	cargo doc --no-deps
	rm -rf ./doc
	cp -r ./target/doc ./doc
	-cat ./custom.css >> doc/main.css

.PHONY: docs mkdocs subst $(DOCCRATES)