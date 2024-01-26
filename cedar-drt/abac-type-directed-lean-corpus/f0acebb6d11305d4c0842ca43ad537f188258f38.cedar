permit(
  principal,
  action == Action::"action",
  resource == a::"\0\0\0\06"
) when {
  ((true && (action is a)) && false) && false
};
