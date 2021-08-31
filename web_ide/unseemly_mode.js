ace.define(
    'ace/mode/unseemly',
    ['require', 'exports', 'module', 'ace/lib/oop', 'ace/mode/text_highlight_rules'],
    function (require, exports, module) {
        "use strict";

        var oop = require("../lib/oop");
        var TextHighlightRules = require("./text_highlight_rules").TextHighlightRules;
        var TextMode = require("./text").Mode;

        var UnseemlyHighlightRules = function () {
            this.$rules = {
                start:
                    [
                        { token: 'keyword', regex: 'forall|mu_type|Int|Ident|Float|match|enum|struct|fold|unfold|extend_syntax|in|import|capture_language' },
                        { token: 'variable', regex: '([a-zA-Z\\xa1-\\uFFFF](?:[a-zA-Z\\xa1-\\uFFFF]|[0-9]|[_?])*)' },
                        { token: 'keyword.operator', regex: '\'\\[' },
                        { token: 'keyword.operator', regex: '\'\\{' },
                        { token: 'paren.rparen', regex: '([\\]\\)\\}][^\\[\\]\\(\\)\\{\\}\\s;:]*)' },
                        { token: 'paren.lparen', regex: '([^\\[\\]\\(\\)\\{\\}\\s;:]*[\\[\\(\\{])' },
                        { token: 'keyword.operator', regex: ',\\{' },
                        { token: 'keyword.operator', regex: ':' },
                        { token: 'keyword.operator', regex: ',' },
                        { token: 'keyword.operator', regex: ':::\\[' },
                        { token: 'keyword.operator', regex: ':=' },
                        { token: 'keyword.operator', regex: ';' },
                        { token: 'keyword.operator', regex: '<\\-\\-' },
                        { token: 'keyword.operator', regex: '=' },
                        { token: 'keyword.operator', regex: '=>' },
                        { token: 'keyword.operator', regex: '>>' },
                        { token: 'keyword.operator', regex: 'Float' },
                        { token: 'keyword.operator', regex: 'Ident' },
                        { token: 'keyword.operator', regex: 'Int' },
                        { token: 'keyword.operator', regex: 'Nat' },
                        { token: 'keyword.operator', regex: 'String' },
                        { token: 'keyword.operator', regex: '\\(' },
                        { token: 'keyword.operator', regex: '\\)' },
                        { token: 'keyword.operator', regex: '\\*' },
                        { token: 'keyword.operator', regex: '\\*\\*\\[' },
                        { token: 'keyword.operator', regex: '\\*\\[' },
                        { token: 'keyword.operator', regex: '\\+' },
                        { token: 'keyword.operator', regex: '\\+\\[' },
                        { token: 'keyword.operator', regex: '\\->' },
                        { token: 'keyword.operator', regex: '\\-\\{' },
                        { token: 'keyword.operator', regex: '\\.' },
                        { token: 'keyword.operator', regex: '\\.\\.\\.\\[' },
                        { token: 'keyword.operator', regex: '\\.\\[' },
                        { token: 'keyword.operator', regex: '\\.\\{' },
                        { token: 'keyword.operator', regex: '\\[' },
                        { token: 'keyword.operator', regex: '\\]' },
                        { token: 'keyword.operator', regex: '\\]\'' },
                        { token: 'keyword.operator', regex: '\\]:::' },
                        { token: 'keyword.operator', regex: '\\]\\*' },
                        { token: 'keyword.operator', regex: '\\]\\*\\*' },
                        { token: 'keyword.operator', regex: '\\]\\+' },
                        { token: 'keyword.operator', regex: '\\]\\.' },
                        { token: 'keyword.operator', regex: '\\]\\.\\.\\.' },
                        { token: 'keyword.operator', regex: '\\]alt' },
                        { token: 'keyword.operator', regex: '\\]s' },
                        { token: 'string.quoted.double', regex: '\\s*"((?:[^"\\\\]|\\\\"|\\\\\\\\)*)"' },
                        { token: 'keyword.operator', regex: '\\{' },
                        { token: 'keyword.operator', regex: '\\}' },
                        { token: 'keyword.operator', regex: '\\}\'' },
                        { token: 'keyword.operator', regex: '\\},' },
                        { token: 'keyword.operator', regex: '\\}\\-' },
                        { token: 'keyword.operator', regex: '\\}\\.' },
                        { token: 'keyword.operator', regex: '\\}anyways' },
                        { token: 'keyword.operator', regex: '\\}or' },
                        { token: 'keyword.operator', regex: 'alt\\[' },
                        { token: 'keyword.operator', regex: 'anyways\\{' },
                        { token: 'keyword.operator', regex: 'as' },
                        { token: 'keyword.operator', regex: 'capture_language_form' },
                        { token: 'keyword.operator', regex: 'common' },
                        { token: 'keyword.operator', regex: 'extend_syntax' },
                        { token: 'keyword.operator', regex: 'fold' },
                        { token: 'keyword.operator', regex: 'forall' },
                        { token: 'keyword.operator', regex: 'impossible' },
                        { token: 'keyword.operator', regex: 'in' },
                        { token: 'keyword.operator', regex: 'let_type' },
                        { token: 'keyword.operator', regex: 'lit' },
                        { token: 'keyword.operator', regex: 'match' },
                        { token: 'keyword.operator', regex: 'mu_type' },
                        { token: 'keyword.operator', regex: 'nothing' },
                        { token: 'keyword.operator', regex: 'o>' },
                        { token: 'keyword.operator', regex: 'or\\{' },
                        { token: 'keyword.operator', regex: 'pick' },
                        { token: 'keyword.operator', regex: 'prefab_type' },
                        { token: 'keyword.operator', regex: 'prot' },
                        { token: 'keyword.operator', regex: 'reserving' },
                        { token: 'keyword.operator', regex: 's\\[' },
                        { token: 'keyword.operator', regex: 'unfold' },
                        { token: 'keyword.operator', regex: 'vr' },

                        // HACK! the rest of the above were automatically-generated
                        //  from the Unseemly core language.
                        // Comments aren't part of the core language, but are really important,
                        //  so I'll throw them in...
                        { token: 'comment', regex: '#[^\\n|][^\\n]*|#\\|.*?\\|#' },
                    ]
            };

            this.normalizeRules();
        };

        UnseemlyHighlightRules.metaData = {
            fileTypes: ['unseemly'],
            name: 'Unseemly',
            scopeName: 'source.unseemly'
        };

        oop.inherits(UnseemlyHighlightRules, TextHighlightRules);

        var Mode = function() {
            this.HighlightRules = UnseemlyHighlightRules;
            // TODO: this.foldingRules
            // TODO: this.$behavior
        };
        oop.inherits(Mode, TextMode);

        exports.Mode = Mode;

    });
