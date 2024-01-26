permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && ({"\u{15}\u{15}\u{15}\u{15}\u{15}\u{15}\u{15}\u{15}": "\u{15}\u{15}\u{15}\u{15}\u{15}\u{15}\u{15}\u{15}"}[""])) && (a::""["\0\0"])
};
