@A(".\0\0\0")
@J("")
permit(
  principal is A::a in A::a::"",
  action == A::Action::"6",
  resource
) when {
  true && ({"": true} has "")
};
