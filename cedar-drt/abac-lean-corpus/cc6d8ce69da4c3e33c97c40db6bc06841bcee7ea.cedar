@A("")
@V("")
permit(
  principal,
  action in [s::r::A::r::Action::"action"],
  resource == s::r::A::r::a::"\0\0\u{11}\0"
) when {
  true
};
