theories/Syntax/Level.vo theories/Syntax/Level.glob theories/Syntax/Level.v.beautified theories/Syntax/Level.required_vo: theories/Syntax/Level.v 
theories/Syntax/Level.vos theories/Syntax/Level.vok theories/Syntax/Level.required_vos: theories/Syntax/Level.v 
theories/Syntax/Term.vo theories/Syntax/Term.glob theories/Syntax/Term.v.beautified theories/Syntax/Term.required_vo: theories/Syntax/Term.v theories/Syntax/Level.vo
theories/Syntax/Term.vos theories/Syntax/Term.vok theories/Syntax/Term.required_vos: theories/Syntax/Term.v theories/Syntax/Level.vos
theories/Syntax/Subst.vo theories/Syntax/Subst.glob theories/Syntax/Subst.v.beautified theories/Syntax/Subst.required_vo: theories/Syntax/Subst.v theories/Syntax/Term.vo
theories/Syntax/Subst.vos theories/Syntax/Subst.vok theories/Syntax/Subst.required_vos: theories/Syntax/Subst.v theories/Syntax/Term.vos
theories/Syntax/NormalForms.vo theories/Syntax/NormalForms.glob theories/Syntax/NormalForms.v.beautified theories/Syntax/NormalForms.required_vo: theories/Syntax/NormalForms.v theories/Syntax/Subst.vo
theories/Syntax/NormalForms.vos theories/Syntax/NormalForms.vok theories/Syntax/NormalForms.required_vos: theories/Syntax/NormalForms.v theories/Syntax/Subst.vos
theories/Syntax/Reduction.vo theories/Syntax/Reduction.glob theories/Syntax/Reduction.v.beautified theories/Syntax/Reduction.required_vo: theories/Syntax/Reduction.v theories/Syntax/NormalForms.vo
theories/Syntax/Reduction.vos theories/Syntax/Reduction.vok theories/Syntax/Reduction.required_vos: theories/Syntax/Reduction.v theories/Syntax/NormalForms.vos
theories/Syntax/Weakening.vo theories/Syntax/Weakening.glob theories/Syntax/Weakening.v.beautified theories/Syntax/Weakening.required_vo: theories/Syntax/Weakening.v theories/Syntax/Commute.vo
theories/Syntax/Weakening.vos theories/Syntax/Weakening.vok theories/Syntax/Weakening.required_vos: theories/Syntax/Weakening.v theories/Syntax/Commute.vos
theories/Syntax/Commute.vo theories/Syntax/Commute.glob theories/Syntax/Commute.v.beautified theories/Syntax/Commute.required_vo: theories/Syntax/Commute.v theories/Syntax/Reduction.vo
theories/Syntax/Commute.vos theories/Syntax/Commute.vok theories/Syntax/Commute.required_vos: theories/Syntax/Commute.v theories/Syntax/Reduction.vos
theories/Typing/Context.vo theories/Typing/Context.glob theories/Typing/Context.v.beautified theories/Typing/Context.required_vo: theories/Typing/Context.v theories/Syntax/Weakening.vo
theories/Typing/Context.vos theories/Typing/Context.vok theories/Typing/Context.required_vos: theories/Typing/Context.v theories/Syntax/Weakening.vos
theories/Typing/Declarative.vo theories/Typing/Declarative.glob theories/Typing/Declarative.v.beautified theories/Typing/Declarative.required_vo: theories/Typing/Declarative.v theories/Typing/Context.vo
theories/Typing/Declarative.vos theories/Typing/Declarative.vok theories/Typing/Declarative.required_vos: theories/Typing/Declarative.v theories/Typing/Context.vos
theories/Typing/Properties.vo theories/Typing/Properties.glob theories/Typing/Properties.v.beautified theories/Typing/Properties.required_vo: theories/Typing/Properties.v theories/Typing/Declarative.vo
theories/Typing/Properties.vos theories/Typing/Properties.vok theories/Typing/Properties.required_vos: theories/Typing/Properties.v theories/Typing/Declarative.vos
theories/Typing/TypedRed.vo theories/Typing/TypedRed.glob theories/Typing/TypedRed.v.beautified theories/Typing/TypedRed.required_vo: theories/Typing/TypedRed.v theories/Typing/Properties.vo
theories/Typing/TypedRed.vos theories/Typing/TypedRed.vok theories/Typing/TypedRed.required_vos: theories/Typing/TypedRed.v theories/Typing/Properties.vos
theories/Typing/Generic.vo theories/Typing/Generic.glob theories/Typing/Generic.v.beautified theories/Typing/Generic.required_vo: theories/Typing/Generic.v theories/Typing/TypedRed.vo
theories/Typing/Generic.vos theories/Typing/Generic.vok theories/Typing/Generic.required_vos: theories/Typing/Generic.v theories/Typing/TypedRed.vos
theories/LogRel/Def.vo theories/LogRel/Def.glob theories/LogRel/Def.v.beautified theories/LogRel/Def.required_vo: theories/LogRel/Def.v theories/Typing/Generic.vo
theories/LogRel/Def.vos theories/LogRel/Def.vok theories/LogRel/Def.required_vos: theories/LogRel/Def.v theories/Typing/Generic.vos
theories/LogRel/Escape.vo theories/LogRel/Escape.glob theories/LogRel/Escape.v.beautified theories/LogRel/Escape.required_vo: theories/LogRel/Escape.v theories/LogRel/Def.vo
theories/LogRel/Escape.vos theories/LogRel/Escape.vok theories/LogRel/Escape.required_vos: theories/LogRel/Escape.v theories/LogRel/Def.vos
theories/LogRel/Basics.vo theories/LogRel/Basics.glob theories/LogRel/Basics.v.beautified theories/LogRel/Basics.required_vo: theories/LogRel/Basics.v theories/LogRel/Escape.vo
theories/LogRel/Basics.vos theories/LogRel/Basics.vok theories/LogRel/Basics.required_vos: theories/LogRel/Basics.v theories/LogRel/Escape.vos
