@A(".")
@J("")
permit(
  principal in A::a::"",
  action in [A::Action::"6"],
  resource
) when {
  ((true && (resource in A::a::"\0\0\0\0\0\0\0\0\u{6}\0\0")) && true) && (if (resource in A::a::"\0\0\0\0\0\0\0\0\u{6}\0\0") then true else (if false then false else ([].containsAny([]))))
};
