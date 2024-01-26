permit(
  principal == a::"",
  action,
  resource in a::"11111111111\0\0\0\0\0\0\0\0\06"
) when {
  ((true && (if (if false then false else false) then (!false) else true)) && true) && true
};
