permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  true && (a::"6" has "\0\0\0\06H\0\0266>6666\0\0\0\0\0\u{2}\0\0\0")
};
