forbid(
  principal in rsss::a::"66666666?666666\u{1}\0\06\0\0\0\0\t66666",
  action in [rsss::Action::"action"],
  resource is rsss::a in rsss::a::""
) when {
  true && ((if (principal has "66\u{12}z666") then action else rsss::a::"66666666?666666\u{1}\0\06\0\0\0\0\t66666") has "")
};
